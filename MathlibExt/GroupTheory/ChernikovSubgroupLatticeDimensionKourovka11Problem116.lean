/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.Chernikov
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.Projection
import Mathlib.Order.Extension.Linear
import Mathlib.Order.PiLex
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Order.UpperLower.Closure

/-!
# Order dimension of subgroup lattices of Chernikov groups

We prove the positive answer to Shevrin's Problem 11.116 in the Kourovka Notebook. When a
Chernikov group contains no quasicyclic square, subgroup inclusion is the intersection of
finitely many linear orders. The proof separates the quasicyclic factors by prime and
records the intersection of a subgroup with each coset of a finite-index abelian subgroup.

## Record carried over from the retired wanted module

From `WantedExt/GroupTheory/ChernikovSubgroupLatticeDimensionKourovka11Problem116Wanted.lean`:

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 11.116 (L. N. Shevrin). UnsolvedMath record
UM-00700808 (`KOU-11.116`), dataset ulamai/UnsolvedMath v1.8.0.

A quasicyclic group is an infinite abelian group all of whose proper subgroups are finite (this
characterizes the Prüfer groups `C_{p^∞}`). A Chernikov group is `IsChernikov` of
`GroupClassesShared`: it has an abelian subgroup of finite index with the minimal condition on
subgroups. Since an abelian group with the minimal condition is a direct product of finitely many
quasicyclic groups and a finite group, this is the same as having a normal subgroup of finite index
isomorphic to a finite direct product of quasicyclic groups; finite groups are the case of zero
factors. "Contains a direct product of two quasicyclic groups over the same prime" is read as an
embedding of `Q × Q` for a quasicyclic `Q`, since quasicyclic groups over one prime are isomorphic.
Finite dimension means the subgroup order is the intersection of finitely many linear orders on
`Subgroup G` (Dushnik-Miller dimension).
-/

namespace MathlibExt.GroupTheory.ChernikovSubgroupLatticeDimensionKourovka11Problem116Wanted

@[expose] public section

/-- **Quasicyclic group.** A group $Q$ is quasicyclic if it is abelian and infinite and every
proper subgroup of $Q$ is finite.

These are exactly the Prüfer groups $C_{p^\infty}$ for primes $p$. -/
def IsQuasicyclic (Q : Type*) [Group Q] : Prop :=
  (∀ a b : Q, a * b = b * a) ∧ Infinite Q ∧ ∀ K : Subgroup Q, K ≠ ⊤ → (K : Set Q).Finite

open MathlibExt.GroupTheory.GroupClassesShared (IsChernikov)

/-- **Groups containing the square of a quasicyclic group.** A group $G$ contains a direct product
of two quasicyclic groups over the same prime when there are a quasicyclic group $Q$ and an
injective group homomorphism $Q \times Q \to G$ (quasicyclic groups over the same prime are
isomorphic). -/
def ContainsQuasicyclicSquare (G : Type*) [Group G] : Prop :=
  ∃ (Q : Type) (_ : Group Q), IsQuasicyclic Q ∧ ∃ f : Q × Q →* G, Function.Injective f

/-- A partially ordered set has finite (order) dimension: its order relation is the intersection
of finitely many linear orders on the same set. -/
def HasFiniteOrderDimension (P : Type*) [PartialOrder P] : Prop :=
  ∃ (n : ℕ) (L : Fin n → LinearOrder P), ∀ x y : P, x ≤ y ↔ ∀ i, (L i).le x y

/-- **Shevrin's problem on the dimension of subgroup lattices of Chernikov groups.** The
proposition that for every Chernikov group $G$ that does not contain a direct product of two
quasicyclic groups over the same prime (that is, there is no quasicyclic group $Q$ with an
injective homomorphism $Q \times Q \to G$), the lattice of subgroups of $G$ has finite order
dimension: the inclusion order on the subgroups of $G$ is the intersection of finitely many linear
orders on that set. This is Kourovka Problem 11.116 (L. N. Shevrin). -/
def chernikovSubgroupLatticeFiniteDimension : Prop :=
  ∀ (G : Type) [Group G], IsChernikov G → ¬ ContainsQuasicyclicSquare G →
    HasFiniteOrderDimension (Subgroup G)

end

/- Break ties in each chain coordinate with a linear extension of the original order. -/
private theorem ofCoordinates {P ι : Type*} [PartialOrder P] [Finite ι]
    {C : ι → Type*} [∀ i, LinearOrder (C i)] (f : P → ∀ i, C i)
    (hf : ∀ x y, x ≤ y ↔ ∀ i, f x i ≤ f y i) : HasFiniteOrderDimension P := by
  classical
  let := Fintype.ofFinite ι
  let z (i : ι) (x : P) := toLex (f x i, toLinearExtension x)
  have hinj (i : ι) : Function.Injective (z i) := fun _ _ h ↦
    congrArg Prod.snd (toLex.injective h)
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i ↦ LinearOrder.lift' (z (e.symm i)) (hinj _), fun x y ↦ ?_⟩
  constructor
  · intro h i
    exact Prod.Lex.toLex_mono ⟨(hf x y).mp h _, toLinearExtension.monotone h⟩
  · intro h
    apply (hf x y).mpr
    intro i
    have hi := Prod.Lex.monotone_fst _ _ (h (e i))
    change f x (e.symm (e i)) ≤ f y (e.symm (e i)) at hi
    rwa [e.symm_apply_apply] at hi

private theorem infiniteRange {Q B : Type*} [AddCommGroup Q] [AddCommGroup B]
    [Infinite Q] (hQ : ∀ H : AddSubgroup Q, H ≠ ⊤ → Finite H)
    (f : Q →+ B) (hf : f ≠ 0) : Infinite f.range := by
  rw [← not_finite_iff_infinite]
  intro h
  have hk := hQ f.ker (fun heq ↦ hf (AddMonoidHom.ker_eq_top_iff.mp heq))
  exact not_finite_iff_infinite.mpr (inferInstance : Infinite Q)
    (f.finite_iff_finite_ker_range.mpr ⟨hk, h⟩)

/- A nonzero character has finite kernel. Its image in the rational circle is infinite,
so multiplication by a positive integer still has infinite image. -/
private theorem minimalInfiniteDivisible (Q : Type*) [AddCommGroup Q] [Infinite Q]
    (hQ : ∀ H : AddSubgroup Q, H ≠ ⊤ → Finite H) : Nonempty (DivisibleBy Q ℤ) := by
  classical
  obtain ⟨a, ha⟩ := exists_ne (0 : Q)
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero ha
  change Q →+ AddCircle (1 : ℚ) at c
  have hc' : c ≠ 0 := fun e ↦ hc (DFunLike.congr_fun e a)
  have hcinf := infiniteRange hQ c hc'
  let := divisibleByOfSMulRightSurj Q ℕ (fun {n} hn ↦ by
    let m : Q →+ Q := n • AddMonoidHom.id Q
    change Function.Surjective m
    apply AddMonoidHom.range_eq_top.mp
    by_contra hproper
    have hm := hQ _ hproper
    have hcomp : c.comp m ≠ 0 := by
      intro e
      have ht := AddCircle.finite_torsion (1 : ℚ) (Nat.pos_of_ne_zero hn)
      have hf : (c.range : Set (AddCircle (1 : ℚ))).Finite := ht.subset (by
        rintro _ ⟨x, rfl⟩
        simpa [m] using DFunLike.congr_fun e x)
      exact not_finite_iff_infinite.mpr hcinf (Set.finite_coe_iff.mpr hf)
    have hinf := infiniteRange hQ (c.comp m) hcomp
    have heq : (c.comp m).range = m.range.map c := AddMonoidHom.range_comp _ _
    have hfin : Finite (m.range.map c) := Set.finite_coe_iff.mpr
      ((Set.finite_coe_iff.mp hm).image c)
    exact not_finite_iff_infinite.mpr hinf (heq ▸ hfin))
  exact ⟨AddGroup.divisibleByIntOfDivisibleByNat Q⟩

private theorem splitsMinimal (A : Type*) [AddCommGroup A] (P : Submodule ℤ A) [Infinite P]
    (hP : ∀ K : AddSubgroup P, K ≠ ⊤ → Finite K) :
    ∃ B : Submodule ℤ A, IsCompl P B ∧ Nonempty (P × B ≃+ A) := by
  let := (minimalInfiniteDivisible P hP).some
  obtain ⟨r, hr⟩ := (Module.Baer.of_divisible P).extension_property P.subtype
    P.injective_subtype LinearMap.id
  have hc := LinearMap.isCompl_of_proj (f := r) (fun x ↦ LinearMap.congr_fun hr x)
  exact ⟨r.ker, hc, ⟨(P.prodEquivOfIsCompl r.ker hc).toAddEquiv⟩⟩

/- Order the points by their lexicographic profiles of common containing sets. Each member
of the family is convex in this order and is recovered from its lower and upper closures. -/
private theorem laminarDimension {X : Type*} (F : Set (Set X))
    (nested : ∀ s t : F, (s.val ∩ t.val).Nonempty → s.val ⊆ t.val ∨ t.val ⊆ s.val) :
    HasFiniteOrderDimension F := by
  classical
  obtain ⟨ord, wf⟩ := exists_wellFoundedLT X
  let B := LinearExtension (Set F)
  let d (z x : X) : B := toLinearExtension {U : F | z ∈ U.val ∧ x ∈ U.val}
  let T := Lex (X → B)
  let f (x : X) : T := toLex fun z ↦ d z x
  have outside (s : F) {z a b : X} (hz : z ∉ s.val) (ha : a ∈ s.val) (hb : b ∈ s.val) :
      d z a = d z b := by
    apply congrArg toLinearExtension
    ext U
    have aux {u v : X} (hu : u ∈ s.val) (hv : v ∈ s.val) (hzU : z ∈ U.val) (huU : u ∈ U.val) :
        v ∈ U.val := ((nested s U ⟨u, hu, huU⟩).resolve_right (fun h ↦ hz (h hzU))) hv
    exact ⟨fun ⟨hzU, h⟩ ↦ ⟨hzU, aux ha hb hzU h⟩, fun ⟨hzU, h⟩ ↦ ⟨hzU, aux hb ha hzU h⟩⟩
  have inside (s : F) {z a w : X} (hz : z ∈ s.val) (ha : a ∈ s.val) (hw : w ∉ s.val) :
      d z w < d z a := by
    have h : StrictMono (@toLinearExtension (Set F) _) :=
      toLinearExtension.monotone.strictMono_of_injective (fun _ _ e ↦ e)
    apply h
    apply lt_of_le_not_ge
    · rintro U ⟨hzU, hwU⟩
      exact ⟨hzU, ((nested s U ⟨z, hz, hzU⟩).resolve_right (fun h ↦ hw (h hwU))) ha⟩
    · intro hsub
      exact hw (hsub (show s ∈ {U : F | z ∈ U.val ∧ a ∈ U.val} from ⟨hz, ha⟩)).2
  have convex (s : F) {a b w : X} (ha : a ∈ s.val) (hb : b ∈ s.val)
      (hleft : f a ≤ f w) (hright : f w ≤ f b) : w ∈ s.val := by
    by_contra hw
    have hne : f a ≠ f w := fun h ↦
      (inside s ha ha hw).ne' (congrArg (fun t : T ↦ ofLex t a) h)
    obtain ⟨z, hprev, hz⟩ := lt_of_le_of_ne hleft hne
    apply (not_lt_of_ge hright : ¬f b < f w)
    refine ⟨z, fun j hj ↦ ?_, ?_⟩
    · have hjout : j ∉ s.val := fun h ↦ (inside s h ha hw).ne' (hprev j hj)
      exact (outside s hjout hb ha).trans (hprev j hj)
    · have hzout : z ∉ s.val := fun h ↦ (inside s h ha hw).not_gt hz
      change d z b < d z w
      rw [outside s hzout hb ha]
      exact hz
  let C : Bool → Type _ | false => LowerSet T | true => (UpperSet T)ᵒᵈ
  let inst : ∀ i, LinearOrder (C i) | false => inferInstanceAs (LinearOrder (LowerSet T))
                                    | true => inferInstanceAs (LinearOrder (UpperSet T)ᵒᵈ)
  let g (s : F) : (i : Bool) → C i
    | false => lowerClosure (f '' s.val)
    | true => OrderDual.toDual (upperClosure (f '' s.val))
  refine @ofCoordinates F Bool _ _ C inst g (fun s t ↦ ?_)
  constructor
  · rintro h (_ | _)
    · exact lowerClosure_mono (Set.image_mono h)
    · exact upperClosure_anti (Set.image_mono h)
  · intro h w hw
    have hsrc : f w ∈ f '' s.val := ⟨w, hw, rfl⟩
    have hL : f w ∈ lowerClosure (f '' t.val) :=
      LowerSet.coe_subset_coe.mpr (h false) (subset_lowerClosure hsrc)
    have hU : f w ∈ upperClosure (f '' t.val) :=
      UpperSet.coe_subset_coe.mpr (h true) (subset_upperClosure hsrc)
    obtain ⟨_, ⟨a, ha, rfl⟩, hleft⟩ := hU
    obtain ⟨_, ⟨b, hb, rfl⟩, hright⟩ := hL
    exact convex t ha hb hleft hright

/- Multiplication by the kernel order factors through the character image. Divisibility
extends this map from the image to the entire rational circle. -/
private theorem circleCover (Q : Type*) [AddCommGroup Q] [Infinite Q]
    (hQ : ∀ H : AddSubgroup Q, H ≠ ⊤ → Finite H) :
    ∃ f : AddCircle (1 : ℚ) →+ Q, Function.Surjective f := by
  classical
  let := (minimalInfiniteDivisible Q hQ).some
  obtain ⟨a, ha⟩ := exists_ne (0 : Q)
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero ha
  change Q →+ AddCircle (1 : ℚ) at c
  have hk := hQ c.ker (fun e ↦ hc (DFunLike.congr_fun (AddMonoidHom.ker_eq_top_iff.mp e) a))
  let n := Nat.card c.ker
  let m : Q →+ Q := (n : ℤ) • AddMonoidHom.id Q
  have hm : c.rangeRestrict.ker ≤ m.ker := by
    intro x hx
    rw [AddMonoidHom.ker_rangeRestrict] at hx
    simpa [m, n, AddMonoidHom.mem_ker] using
      congrArg Subtype.val (card_nsmul_eq_zero' (x := (⟨x, hx⟩ : c.ker)))
  let b := c.rangeRestrict.liftOfSurjective c.rangeRestrict_surjective ⟨m, hm⟩
  obtain ⟨f, hf⟩ := (Module.Baer.of_divisible Q).extension_property_addMonoidHom
    c.range.subtype c.range.subtype_injective b
  refine ⟨f, fun x ↦ ?_⟩
  obtain ⟨y, hy⟩ := DivisibleBy.surjective_smul Q ℤ (n := (n : ℤ))
    (Int.natCast_ne_zero.mpr (Nat.card_pos (α := c.ker)).ne') x
  refine ⟨c y, ?_⟩
  have hfb := DFunLike.congr_fun hf (c.rangeRestrict y)
  exact hfb.trans ((AddMonoidHom.liftOfRightInverse_comp_apply ..).trans hy)

/- The primary component containing an element of prime order is infinite: multiplication
by that prime is surjective on the component and has nontrivial kernel. -/
private theorem primeComponent (Q : Type*) [AddCommGroup Q] [Infinite Q]
    (hQ : ∀ H : AddSubgroup Q, H ≠ ⊤ → Finite H) :
    ∃ p : ℕ, p.Prime ∧ (∃ a : Q, addOrderOf a = p) ∧
      ∀ x : Q, ∃ k : ℕ, addOrderOf x = p ^ k := by
  classical
  let := (minimalInfiniteDivisible Q hQ).some
  obtain ⟨f, hf⟩ := circleCover Q hQ
  obtain ⟨a, ha⟩ := exists_ne (0 : Q)
  have hfin : IsOfFinAddOrder a := by
    obtain ⟨u, rfl⟩ := hf a
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective u
    apply f.isOfFinAddOrder
    apply addOrderOf_pos_iff.mp
    have he := AddCircle.addOrderOf_coe_rat (p := (1 : ℚ)) (q := r)
    have he' : addOrderOf (r : AddCircle (1 : ℚ)) = r.den := by simpa using he
    rw [he']
    exact r.den_pos
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (AddMonoid.addOrderOf_eq_one_iff.not.mpr ha)
  let b := (addOrderOf a / p) • a
  have hb : addOrderOf b = p := by
    dsimp only [b]
    rw [addOrderOf_nsmul_of_dvd _ (Nat.div_dvd_of_dvd hd),
      Nat.div_div_self hd hfin.addOrderOf_pos.ne']
    exact (Nat.div_pos (Nat.le_of_dvd hfin.addOrderOf_pos hd) hp.pos).ne'
  let P := AddCommGroup.primaryComponent Q p
  have hP : P = ⊤ := by
    by_contra hproper
    have := hQ P hproper
    have hsur : Function.Surjective (fun x : P ↦ p • x) := by
      intro x
      obtain ⟨y, hy⟩ := DivisibleBy.surjective_smul Q ℤ (n := (p : ℤ))
        (Int.natCast_ne_zero.mpr hp.ne_zero) x.val
      change (p : ℤ) • y = x.val at hy
      rw [natCast_zsmul] at hy
      obtain ⟨k, hk⟩ := x.property
      refine ⟨⟨y, k + 1, ?_⟩, Subtype.ext hy⟩
      rw [pow_succ, mul_smul, hy, hk]
    have hinj := Finite.injective_iff_surjective.mpr hsur
    have hpb : p • b = 0 := hb ▸ addOrderOf_nsmul_eq_zero b
    let b' : P := ⟨b, 1, by simpa using hpb⟩
    have hzero : b' = 0 := hinj (by apply Subtype.ext; simpa [b'] using hpb)
    have hb0 : b = 0 := congrArg Subtype.val hzero
    simp [hb0, hp.ne_one.symm] at hb
  have : Fact p.Prime := ⟨hp⟩
  exact ⟨p, hp, ⟨b, hb⟩, fun x ↦ AddCommGroup.mem_primaryComponent_iff_addOrderOf.mp
    (show x ∈ P from hP ▸ AddSubgroup.mem_top _)⟩

/- Lift two elements to rationals and use a common denominator to put them in one cyclic
subgroup. Their cyclic subgroups correspond to divisors of the same prime power. -/
private theorem quasicyclicChain (Q : Type*) [AddCommGroup Q] [Infinite Q]
    (hQ : ∀ H : AddSubgroup Q, H ≠ ⊤ → Finite H) :
    ∀ H K : AddSubgroup Q, H ≤ K ∨ K ≤ H := by
  classical
  obtain ⟨p, hp, _, hpow⟩ := primeComponent Q hQ
  obtain ⟨c, hc⟩ := circleCover Q hQ
  let f := c.comp (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)))
  have hf : Function.Surjective f := hc.comp QuotientAddGroup.mk_surjective
  intro H K
  by_contra! h
  obtain ⟨a, ha, hna⟩ := IsConcreteLE.not_le_iff_exists.mp h.1
  obtain ⟨b, hb, hnb⟩ := IsConcreteLE.not_le_iff_exists.mp h.2
  obtain ⟨r, rfl⟩ := hf a
  obtain ⟨s, rfl⟩ := hf b
  let z := f (1 / (r.den * s.den))
  let i : ℤ := r.num * s.den
  let j : ℤ := s.num * r.den
  have hi : i • z = f r := by
    rw [← map_zsmul]
    apply congrArg f
    change (r.num * ↑s.den : ℤ) • (1 / ((r.den : ℚ) * s.den)) = r
    apply Eq.trans _ r.num_div_den
    rw [zsmul_eq_mul]
    push_cast
    field_simp
  have hj : j • z = f s := by
    rw [← map_zsmul]
    apply congrArg f
    change (s.num * ↑r.den : ℤ) • (1 / ((r.den : ℚ) * s.den)) = s
    apply Eq.trans _ s.num_div_den
    rw [zsmul_eq_mul]
    push_cast
    field_simp
  obtain ⟨k, hk⟩ := hpow z
  have he (m : ℤ) : ∃ e ≤ k, m.gcd (addOrderOf z) = p ^ e :=
    (Nat.dvd_prime_pow hp).mp (hk ▸ Int.gcd_dvd_natAbs_right m ↑(addOrderOf z))
  obtain ⟨u, _, hu⟩ := he i
  obtain ⟨v, _, hv⟩ := he j
  rcases le_total u v with huv | hvu
  · apply hnb
    have hle := (AddSubgroup.zmultiples_le_zmultiples_iff z j i).mpr
      (hu ▸ hv ▸ pow_dvd_pow p huv)
    exact (AddSubgroup.zmultiples_le.mpr (hi ▸ ha)) (hle (hj ▸ AddSubgroup.mem_zmultiples _))
  · apply hna
    have hle := (AddSubgroup.zmultiples_le_zmultiples_iff z i j).mpr
      (hv ▸ hu ▸ pow_dvd_pow p hvu)
    exact (AddSubgroup.zmultiples_le.mpr (hj ▸ hb)) (hle (hi ▸ AddSubgroup.mem_zmultiples _))

/- If the element orders share a prime, identify two subgroups of that order. Extend
the identification by divisibility. The chain condition forces the extension to be injective. -/
private theorem separatedOrders {Q D : Type} [AddCommGroup Q] [AddCommGroup D] [Infinite Q]
    [DivisibleBy D ℤ] (hQ : ∀ H : AddSubgroup Q, H ≠ ⊤ → Finite H) (ht : IsAddTorsion D)
    (no : ∀ f : Q →+ D, ¬Function.Injective f) :
    ∀ x : Q, ∀ y : D, (addOrderOf x).Coprime (addOrderOf y) := by
  obtain ⟨p, hp, ⟨a, ha⟩, hprimary⟩ := primeComponent Q hQ
  intro x y
  obtain ⟨k, hk⟩ := hprimary x
  rw [hk]
  apply Nat.Coprime.pow_left
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  let b := (addOrderOf y / p) • y
  have hpos := (ht y).addOrderOf_pos
  have hb : addOrderOf b = p := by
    dsimp only [b]
    rw [addOrderOf_nsmul_of_dvd _ (Nat.div_dvd_of_dvd hd), Nat.div_div_self hd hpos.ne']
    exact (Nat.div_pos (Nat.le_of_dvd hpos hd) hp.pos).ne'
  let U := AddSubgroup.zmultiples a
  let V := AddSubgroup.zmultiples b
  have hc : Nat.card U = Nat.card V := by simp [U, V, Nat.card_zmultiples, ha, hb]
  let e : U ≃+ V := (zmodAddCyclicAddEquiv inferInstance).symm.trans
    ((ZMod.ringEquivCongr hc).toAddEquiv.trans (zmodAddCyclicAddEquiv inferInstance))
  obtain ⟨f, hf⟩ := (Module.Baer.of_divisible D).extension_property_addMonoidHom
    U.subtype U.subtype_injective (V.subtype.comp e.toAddMonoidHom)
  have hinj : Function.Injective (f.comp U.subtype) := hf ▸ V.subtype_injective.comp e.injective
  have hker : f.ker ≤ U := (quasicyclicChain Q hQ f.ker U).resolve_right (by
    intro h
    have he : (⟨a, AddSubgroup.mem_zmultiples _⟩ : U) = 0 :=
      hinj ((h (AddSubgroup.mem_zmultiples a) : f a = 0).trans (map_zero _).symm)
    have : a = 0 := congrArg Subtype.val he
    simp [this, hp.ne_one.symm] at ha)
  apply no f
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  have he : (⟨x, hker hx⟩ : U) = 0 := hinj (hx.trans (map_zero _).symm)
  exact congrArg Subtype.val he

private abbrev ACosets (A : Type*) [AddCommGroup A] :=
  {s : Set A // s = ∅ ∨ ∃ (H : AddSubgroup A) (a : A), s = {x | x - a ∈ H}}

private theorem chainCosets {A : Type*} [AddCommGroup A]
    (h : ∀ H K : AddSubgroup A, H ≤ K ∨ K ≤ H) : HasFiniteOrderDimension (ACosets A) := by
  apply laminarDimension (X := A) {s | s = ∅ ∨
    ∃ (H : AddSubgroup A) (a : A), s = {x | x - a ∈ H}}
  rintro ⟨s, hs⟩ ⟨t, ht⟩ ⟨w, hws, hwt⟩
  change w ∈ s at hws
  change w ∈ t at hwt
  rcases hs with rfl | ⟨H, a, rfl⟩
  · exact hws.elim
  rcases ht with rfl | ⟨K, b, rfl⟩
  · exact hwt.elim
  have inc {H K : AddSubgroup A} {a b : A} (hle : H ≤ K) (h1 : w - a ∈ H)
      (h2 : w - b ∈ K) : {x | x - a ∈ H} ⊆ {x | x - b ∈ K} := by
    intro x hx
    have he := K.add_mem (K.sub_mem (hle hx) (hle h1)) h2
    change x - b ∈ K
    rwa [show x - a - (w - a) + (w - b) = x - b by abel] at he
  exact (h H K).imp (inc · hws hwt) (inc · hwt hws)

private def cosetImage {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (s : ACosets A) : ACosets B := by
  refine ⟨f '' s.val, ?_⟩
  obtain ⟨s, rfl | ⟨H, a, rfl⟩⟩ := s
  · exact Or.inl (Set.image_empty _)
  right
  refine ⟨H.map f, f a, Set.ext fun y ↦ ?_⟩
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x - a, hx, map_sub f ..⟩
  · rintro ⟨v, hv, he⟩
    exact ⟨v + a, by simpa using hv, by simp [he]⟩

/- Coprime element orders let us recover the components of a subgroup element by taking
integer multiples. Each coset is then the product of its projections. -/
private theorem cosetProd {A B : Type} [AddCommGroup A] [AddCommGroup B]
    (hc : ∀ a : A, ∀ b : B, (addOrderOf a).Coprime (addOrderOf b))
    (hA : HasFiniteOrderDimension (ACosets A)) (hB : HasFiniteOrderDimension (ACosets B)) :
    HasFiniteOrderDimension (ACosets (A × B)) := by
  classical
  have first (H : AddSubgroup (A × B)) {a : A} {b : B} (h : (a, b) ∈ H) : (a, 0) ∈ H := by
    obtain ⟨i, j, hij⟩ := (hc a b).isCoprime
    have hel : (j * (addOrderOf b : ℤ)) • a = a := by
      have he := congrArg (fun n : ℤ ↦ n • a) hij
      simpa [add_smul, mul_smul] using he
    have he := H.zsmul_mem h (j * (addOrderOf b : ℤ))
    change ((j * (addOrderOf b : ℤ)) • a, (j * (addOrderOf b : ℤ)) • b) ∈ H at he
    simpa only [hel, mul_smul, natCast_zsmul, addOrderOf_nsmul_eq_zero, smul_zero] using he
  have rect (s : ACosets (A × B)) {a : A} {b : B} (ha : a ∈ Prod.fst '' s.val)
      (hb : b ∈ Prod.snd '' s.val) : (a, b) ∈ s.val := by
    obtain ⟨⟨a, u⟩, hu, rfl⟩ := ha
    obtain ⟨⟨v, b⟩, hv, rfl⟩ := hb
    rcases s with ⟨_, he | ⟨H, ⟨c, d⟩, he⟩⟩
    · simp_all
    · subst_vars
      change (a - c, u - d) ∈ H at hu
      change (v - c, b - d) ∈ H at hv
      have h2 := H.sub_mem hv (first H hv)
      simpa using H.add_mem (first H hu) h2
  obtain ⟨n, L, hL⟩ := hA
  obtain ⟨m, M, hM⟩ := hB
  let C : Fin n ⊕ Fin m → Type | .inl _ => ACosets A | .inr _ => ACosets B
  let ord : ∀ i, LinearOrder (C i) | .inl i => L i | .inr j => M j
  let f (s : ACosets (A × B)) : (i : Fin n ⊕ Fin m) → C i
    | .inl _ => cosetImage (AddMonoidHom.fst A B) s
    | .inr _ => cosetImage (AddMonoidHom.snd A B) s
  refine @ofCoordinates _ _ _ _ C ord f (fun s t ↦ ?_)
  constructor
  · rintro h (i | j)
    · exact (hL _ _).mp (Set.image_mono h) i
    · exact (hM _ _).mp (Set.image_mono h) j
  · rintro h ⟨a, b⟩ hab
    have h1 : Prod.fst '' s.val ⊆ Prod.fst '' t.val :=
      (hL _ _).mpr fun i ↦ h (.inl i)
    have h2 : Prod.snd '' s.val ⊆ Prod.snd '' t.val :=
      (hM _ _).mpr fun i ↦ h (.inr i)
    exact rect t (h1 ⟨_, hab, rfl⟩) (h2 ⟨_, hab, rfl⟩)

/- The induction retains a divisible torsion subgroup of finite index whose cosets,
together with the empty set, have finite order dimension. -/
private abbrev HasCore (A : Type) [AddCommGroup A] : Prop :=
  ∃ (D : Type) (_ : AddCommGroup D) (_ : DivisibleBy D ℤ) (f : D →+ A),
    Function.Injective f ∧ f.range.FiniteIndex ∧ IsAddTorsion D ∧
      HasFiniteOrderDimension (ACosets D)

private theorem coreOfFinite (A : Type) [AddCommGroup A] [Finite A] : HasCore A := by
  let D := (⊥ : AddSubgroup A)
  let := divisibleByOfSMulRightSurj D ℤ fun _ x ↦ ⟨0, Subsingleton.elim _ x⟩
  refine ⟨D, inferInstance, inferInstance, D.subtype, D.subtype_injective,
    inferInstance, isAddTorsion_of_finite, chainCosets ?_⟩
  intro H K
  exact Or.inl fun x _ ↦ (Subsingleton.elim (0 : D) x) ▸ K.zero_mem

private theorem existsMinimalAdd (A : Type) [AddCommGroup A] [Infinite A]
    (h : WellFoundedLT (AddSubgroup A)) :
    ∃ Q : AddSubgroup A, Infinite Q ∧ ∀ K : AddSubgroup Q, K ≠ ⊤ → Finite K := by
  classical
  obtain ⟨Q, hQ, hmin⟩ := h.has_min {K : AddSubgroup A | Infinite K}
    ⟨⊤, (AddSubgroup.topEquiv (G := A)).symm.toEquiv.infinite_iff.mp inferInstance⟩
  refine ⟨Q, hQ, fun K hK ↦ ?_⟩
  by_contra hinf
  have := not_finite_iff_infinite.mp hinf
  let e := K.equivMapOfInjective Q.subtype Q.subtype_injective
  have hm : Infinite (K.map Q.subtype) := e.toEquiv.infinite_iff.mp inferInstance
  apply hmin _ hm
  have hlt := (AddSubgroup.map_subtype_lt_map_subtype (G' := Q)).2 (lt_top_iff_ne_top.mpr hK)
  simpa only [AddSubgroup.map_top, AddSubgroup.range_subtype] using hlt

private abbrev SquareFree (A : Type) [AddCommGroup A] : Prop :=
  ∀ (Q : Type) [AddCommGroup Q] [Infinite Q], (∀ H : AddSubgroup Q, H ≠ ⊤ → Finite H) →
    ∀ f : Q × Q →+ A, ¬Function.Injective f

private theorem coreCongr {A B : Type} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (h : HasCore A) : HasCore B := by
  obtain ⟨D, _, _, f, hf, hfi, ht, hd⟩ := h
  refine ⟨D, inferInstance, inferInstance, e.toAddMonoidHom.comp f, e.injective.comp hf, ?_, ht, hd⟩
  rw [AddMonoidHom.range_comp]
  exact AddSubgroup.FiniteIndex.map_of_surjective f.range e.surjective

/- Split off a minimal infinite subgroup and apply descending induction to its complement.
The excluded square gives coprime element orders across the two divisible factors. -/
private theorem abelianCore (A : Type) [AddCommGroup A] (h : WellFoundedLT (AddSubgroup A))
    (hsq : SquareFree A) : HasCore A := by
  classical
  suffices ∀ S : AddSubgroup A, HasCore S from coreCongr AddSubgroup.topEquiv (this ⊤)
  intro S
  induction S using h.induction with
  | ind S ih =>
    cases finite_or_infinite S with
    | inl _ => exact coreOfFinite S
    | inr hInf =>
      have hw : WellFoundedLT (AddSubgroup S) :=
        Subrelation.wf (fun hab ↦ AddSubgroup.map_subtype_lt_map_subtype.mpr hab)
          (InvImage.wf (fun H : AddSubgroup S ↦ H.map S.subtype) h)
      obtain ⟨Q, hQinf, hQ⟩ := existsMinimalAdd S hw
      have : Infinite Q.toIntSubmodule := hQinf
      obtain ⟨B, hc, ⟨e⟩⟩ := splitsMinimal S Q.toIntSubmodule hQ
      have hB : B ≠ ⊤ := by
        intro htop
        have hbot : Q = ⊥ := AddSubgroup.toIntSubmodule.injective
          (by simpa [htop] using hc.disjoint)
        exact not_finite_iff_infinite.mpr hQinf (hbot ▸ inferInstance)
      let be := B.toAddSubgroup.equivMapOfInjective S.subtype S.subtype_injective
      have hlt : B.toAddSubgroup.map S.subtype < S := by
        have hlt := (AddSubgroup.map_subtype_lt_map_subtype (G' := S)).2
          (show B.toAddSubgroup < ⊤ from lt_top_iff_ne_top.mpr (fun he ↦ hB
            (by change B.toAddSubgroup.toIntSubmodule = _; rw [he]; exact map_top _)))
        simpa only [AddSubgroup.map_top, AddSubgroup.range_subtype] using hlt
      obtain ⟨D, _, _, g, hg, hgi, ht, hd⟩ := coreCongr be.symm (ih _ hlt)
      let v : Q × D →+ Q × B := (AddMonoidHom.id Q).prodMap g
      have hv : Function.Injective v := Prod.map_injective.mpr ⟨Function.injective_id, hg⟩
      have hi : v.range.FiniteIndex := by
        constructor
        have hid : (AddMonoidHom.id Q).range = ⊤ :=
          AddMonoidHom.range_eq_top.mpr Function.surjective_id
        simp [v, AddMonoidHom.range_prodMap, AddSubgroup.index_prod, hgi.index_ne_zero, hid]
      have hno (f : Q →+ D) : ¬Function.Injective f := by
        intro hf
        let m := (AddMonoidHom.id Q).prodMap f
        exact hsq Q hQ (S.subtype.comp (e.toAddMonoidHom.comp (v.comp m)))
          (S.subtype_injective.comp (e.injective.comp (hv.comp (Prod.map_injective.mpr
            ⟨Function.injective_id, hf⟩))))
      let := (minimalInfiniteDivisible Q hQ).some
      have htQ : IsAddTorsion Q := by
        obtain ⟨p, hp, _, hpow⟩ := primeComponent Q hQ
        intro x
        obtain ⟨k, hk⟩ := hpow x
        exact addOrderOf_pos_iff.mp (hk ▸ pow_pos hp.pos k)
      apply coreCongr e
      exact ⟨Q × D, inferInstance, inferInstance, v, hv, hi,
        (fun x ↦ IsOfFinAddOrder.prod_mk (htQ x.1) (ht x.2)),
        cosetProd (separatedOrders hQ ht hno) (chainCosets (quasicyclicChain Q hQ)) hd⟩

private def coreSlice {D G : Type} [AddCommGroup D] [Group G] (f : Multiplicative D →* G)
    (H : Subgroup G) (q : G ⧸ f.range) : ACosets D := by
  let S := {x : D | q.out * f (Multiplicative.ofAdd x) ∈ H}
  refine ⟨S, ?_⟩
  rcases S.eq_empty_or_nonempty with h | ⟨a, ha⟩
  · exact Or.inl h
  right
  refine ⟨AddSubgroup.toSubgroup.symm (H.comap f), a, Set.ext fun x ↦ ?_⟩
  let t (x : D) := f (Multiplicative.ofAdd x)
  change q.out * t a ∈ H at ha
  change q.out * t x ∈ H ↔ f (Multiplicative.ofAdd (x - a)) ∈ H
  have he : f (Multiplicative.ofAdd (x - a)) = (t a)⁻¹ * t x := by
    rw [sub_eq_neg_add]
    exact (map_mul f _ _).trans (congrArg (· * t x) (map_inv f _))
  rw [he]
  exact ⟨fun hx ↦ by simpa [mul_assoc] using H.mul_mem (H.inv_mem ha) hx,
    fun hx ↦ by simpa [mul_assoc] using H.mul_mem ha hx⟩

/- Slice each subgroup along the finitely many cosets of the image. The slices, translated
back into the domain, recover subgroup inclusion coordinate by coordinate. -/
private theorem dimensionOfCore {D G : Type} [AddCommGroup D] [Group G]
    (f : Multiplicative D →* G) [f.range.FiniteIndex]
    (hd : HasFiniteOrderDimension (ACosets D)) : HasFiniteOrderDimension (Subgroup G) := by
  classical
  obtain ⟨n, L, hL⟩ := hd
  refine @ofCoordinates _ ((G ⧸ f.range) × Fin n) _ _ (fun _ ↦ ACosets D)
    (fun j ↦ L j.2) (fun H j ↦ coreSlice f H j.1) ?_
  intro H K
  constructor
  · intro h j
    exact (hL _ _).mp (show coreSlice f H j.1 ≤ coreSlice f K j.1 from fun _ he ↦ h he) j.2
  · intro h g hg
    let q : G ⧸ f.range := QuotientGroup.mk g
    have hs : coreSlice f H q ≤ coreSlice f K q := (hL _ _).mpr fun i ↦ h (q, i)
    obtain ⟨⟨_, a, rfl⟩, ha⟩ := QuotientGroup.mk_out_eq_mul f.range g
    have he : q.out * f a⁻¹ = g := by simp [q, ha]
    change ∀ ⦃x : D⦄, q.out * f (Multiplicative.ofAdd x) ∈ H →
      q.out * f (Multiplicative.ofAdd x) ∈ K at hs
    rw [← he] at hg ⊢
    exact hs (x := Multiplicative.toAdd a⁻¹) hg

/-- **Subgroup lattices of Chernikov groups without a quasicyclic square have finite dimension.**
Let $G$ be a Chernikov group, that is, a group with a normal subgroup of finite index isomorphic to
a direct product of finitely many quasicyclic groups (infinite abelian groups all of whose proper
subgroups are finite). Suppose that $G$ does not contain a direct product of two quasicyclic groups
over the same prime: there is no quasicyclic group $Q$ with an injective homomorphism
$Q \times Q \to G$. Then the lattice of subgroups of $G$ has finite order dimension: the inclusion
order on the subgroups of $G$ is the intersection of finitely many linear orders on that set.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem
11.116 (L. N. Shevrin); resolution: M. Kinyon and J. Urban (with Codex gpt-6-astra), Results on
problems from the Kourovka Notebook, preprint, version 4 (19 September 2026), Section 3.9: if `D ⊴
G` has index `m` and `D = C_{p₁^∞} × ⋯ × C_{p_r^∞}` with distinct primes, the subgroup lattice of
`G` embeds in a product of `2rm` chains, so its order dimension is at most `2rm`; the Kourovka
Notebook (21st issue) marks 11.116 solved (AI solution confirmed by P. Shumyatsky),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka-mathematics.pdf.
-/
public theorem chernikovSubgroupLatticeFiniteDimension_holds :
    chernikovSubgroupLatticeFiniteDimension := by
  intro G _ hG hno
  obtain ⟨A, hindex, hab, hw⟩ := hG
  let : CommGroup A := { (inferInstance : Group A) with
    mul_comm := fun x y ↦ Subtype.ext (hab x x.property y y.property) }
  let E := @Subgroup.toAddSubgroup A _
  have hA : WellFoundedLT (AddSubgroup (Additive A)) :=
    Subrelation.wf (fun h ↦ E.symm.strictMono h) (InvImage.wf E.symm hw)
  have hs : SquareFree (Additive A) := by
    intro Q _ hInf hQ f hf
    let e := (MulEquiv.prodMultiplicative Q Q).symm
    let m := A.subtype.comp ((AddMonoidHom.toMultiplicative f).comp e.toMonoidHom)
    apply hno
    refine ⟨Multiplicative Q, inferInstance, ⟨mul_comm, hInf, ?_⟩, m,
      A.subtype_injective.comp (hf.comp e.injective)⟩
    intro K hK
    let K' := AddSubgroup.toSubgroup.symm K
    have hn : K' ≠ ⊤ := fun he ↦
      hK (AddSubgroup.toSubgroup.symm.injective (he.trans (map_top _).symm))
    exact Set.finite_coe_iff.mp (hQ K' hn)
  obtain ⟨D, _, _, f, _, hfi, _, hdim⟩ := abelianCore (Additive A) hA hs
  let m : Multiplicative D →* A := AddMonoidHom.toMultiplicative f
  have hm : m.range.FiniteIndex := ⟨hfi.index_ne_zero⟩
  have : (A.subtype.comp m).range.FiniteIndex := by
    constructor
    rw [MonoidHom.range_comp, Subgroup.index_map_subtype]
    exact mul_ne_zero hm.index_ne_zero hindex.index_ne_zero
  exact dimensionOfCore (A.subtype.comp m) hdim

end MathlibExt.GroupTheory.ChernikovSubgroupLatticeDimensionKourovka11Problem116Wanted
