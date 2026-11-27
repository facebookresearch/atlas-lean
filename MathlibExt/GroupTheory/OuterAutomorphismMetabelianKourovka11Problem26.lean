/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Solvable
import MathlibExt.GroupTheory.ScottishBook142
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Ring.Aut
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Order.Setoid.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Outer automorphism groups of centreless metabelian groups (Kourovka Notebook Problem 11.26)

Kourovka Notebook, Archive of Solved Problems, Problem 11.26 (R. Göbel): does there exist a group
that is not isomorphic to the outer automorphism group of a metabelian group with trivial centre?
The theorem `groupNotOuterAutOfMetabelian_refuted` gives a realization for every group.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.26 (R.
Göbel). UnsolvedMath record UM-00700719 (`KOU-11.26`), dataset ulamai/UnsolvedMath v1.8.0.

`Out(M) ≅ G` is stated without forming the quotient: some surjective homomorphism `Aut(M) → G` has
kernel the inner automorphism group (the range of `MulAut.conj`). Metabelian is `derivedSeries M 2 =
⊥`. The groups `G` and `M` live in `Type`.

The proof starts with Birkhoff's realization of a group as the automorphism group of a binary
relation. Three equivalence relations on the points and edges encode its incidences and distinguish
the points. Congruences modulo 7, 31 and 127 encode these equivalence relations in a ring of
dyadic-valued functions. Its ring automorphisms permute the coordinates and recover exactly the
permutations preserving the three relations.

Finally the affine group of this ring consists of the maps `x ↦ a + u * x` with `u` a unit.
Conjugation accounts for translations and scaling by units. The induced action on the scalars
identifies the outer automorphism group with the ring automorphism group.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.OuterAutomorphismMetabelianKourovka11Problem26Wanted

/-- **Outer automorphism group isomorphic to a given group.** For groups $M$ and $G$, the
statement that $\operatorname{Out}(M) \cong G$, expressed without forming the quotient: there is a
surjective homomorphism $\operatorname{Aut}(M) \to G$ whose kernel is exactly the inner
automorphism group $\operatorname{Inn}(M)$, the image of the conjugation map
$M \to \operatorname{Aut}(M)$. -/
def OutIsoTo (M G : Type*) [Group M] [Group G] : Prop :=
  ∃ φ : MulAut M →* G, Function.Surjective φ ∧ φ.ker = (MulAut.conj (G := M)).range

/-- **A group that is not an outer automorphism group of a centreless metabelian group.** The
statement (Kourovka Problem 11.26, Göbel) that there is a group $G$ such that for every metabelian
group $M$ (one whose second derived subgroup $M''$ is trivial) with trivial centre, the outer
automorphism group $\operatorname{Out}(M)$ is not isomorphic to $G$. -/
def groupNotOuterAutOfMetabelian : Prop :=
  ∃ (G : Type) (_ : Group G), ∀ (M : Type) [Group M], Subgroup.derivedSeries M 2 = ⊥ →
    Subgroup.center M = ⊥ → ¬ OutIsoTo M G

section Partitions

-- A point has itself as both endpoints. The source and target partitions record incidence,
-- and a third partition puts all points in one class and each edge in its own singleton.
private def stabilizer {I : Type} (P : Fin 3 → Setoid I) : Subgroup (Equiv.Perm I) where
  carrier := {f | ∀ k i j, (P k).r i j ↔ (P k).r (f i) (f j)}
  one_mem' := fun _ _ _ ↦ Iff.rfl
  mul_mem' {f g} hf hg k i j := (hg k i j).trans (hf k _ _)
  inv_mem' {f} hf k i j := by simpa using (hf k (f.symm i) (f.symm j)).symm

private abbrev Inc {Z : Type} (X : Set (Z × Z)) := Z ⊕ X

private def src {Z} {X : Set (Z × Z)} : Inc X → Z := Sum.elim id (fun e ↦ e.val.1)
private def dst {Z} {X : Set (Z × Z)} : Inc X → Z := Sum.elim id (fun e ↦ e.val.2)
private def mark {Z} {X : Set (Z × Z)} : Inc X → Option X := Sum.elim (fun _ ↦ none) some

private def parts {Z} (X : Set (Z × Z)) : Fin 3 → Setoid (Inc X) :=
  ![Setoid.ker src, Setoid.ker dst, Setoid.ker mark]

private theorem src_perm {Z} {X : Set (Z × Z)} (e : stabilizer (parts X)) (i j : Inc X) :
    src i = src j ↔ src (e.val i) = src (e.val j) := e.property 0 i j

private theorem dst_perm {Z} {X : Set (Z × Z)} (e : stabilizer (parts X)) (i j : Inc X) :
    dst i = dst j ↔ dst (e.val i) = dst (e.val j) := e.property 1 i j

private theorem mark_perm {Z} {X : Set (Z × Z)} (e : stabilizer (parts X)) (i j : Inc X) :
    mark i = mark j ↔ mark (e.val i) = mark (e.val j) := e.property 2 i j

private theorem point_iff {Z} [Nontrivial Z] {X : Set (Z × Z)} (i : Inc X) :
    (∃ j ≠ i, mark j = mark i) ↔ ∃ z, i = .inl z := by
  cases i with
  | inl z =>
    obtain ⟨w, hw⟩ := exists_ne z
    exact iff_of_true ⟨.inl w, fun h ↦ hw (Sum.inl.inj h), rfl⟩ ⟨z, rfl⟩
  | inr x =>
    apply iff_of_false _ (by simp)
    rintro ⟨j, hj, he⟩
    cases j with
    | inl => contradiction
    | inr y => exact hj (congrArg Sum.inr (Option.some.inj he))

private theorem point_perm {Z} [Nontrivial Z] {X : Set (Z × Z)} (e : stabilizer (parts X))
    (z : Z) : ∃ w, e.val (.inl z) = .inl w := by
  obtain ⟨j, hj, hm⟩ := (point_iff (X := X) (.inl z)).mpr ⟨z, rfl⟩
  apply (point_iff _).mp
  exact ⟨_, fun h ↦ hj (e.val.injective h), (mark_perm e _ _).mp hm⟩

private def restrictPoints {Z} [Nontrivial Z] {X : Set (Z × Z)} (e : stabilizer (parts X)) :
    Equiv.Perm Z where
  toFun z := src (e.val (.inl z))
  invFun z := src (e.val.symm (.inl z))
  left_inv z := by
    obtain ⟨w, hw⟩ := point_perm e z
    dsimp only
    rw [hw]
    change src (e.val.symm (.inl w)) = z
    rw [← hw, Equiv.symm_apply_apply]
    rfl
  right_inv z := by
    obtain ⟨w, hw⟩ := point_perm e⁻¹ z
    change e.val.symm (.inl z) = .inl w at hw
    dsimp only
    rw [hw]
    change src (e.val (.inl w)) = z
    rw [← hw, Equiv.apply_symm_apply]
    rfl

private theorem on_point {Z} [Nontrivial Z] {X : Set (Z × Z)} (e : stabilizer (parts X)) (z : Z) :
    e.val (.inl z) = .inl (restrictPoints e z) := by
  obtain ⟨w, hw⟩ := point_perm e z
  change e.val (.inl z) = .inl (src (e.val (.inl z)))
  rw [hw]
  rfl

private theorem on_edge {Z} [Nontrivial Z] {X : Set (Z × Z)} (e : stabilizer (parts X)) (a : X) :
    ∃ b : X, e.val (.inr a) = .inr b ∧ b.val = (restrictPoints e a.val.1,
      restrictPoints e a.val.2) := by
  have hs := (src_perm e (.inr a) (.inl a.val.1)).mp rfl
  have ht := (dst_perm e (.inr a) (.inl a.val.2)).mp rfl
  rw [on_point] at hs ht
  cases hv : e.val (.inr a) with
  | inl z =>
    obtain ⟨w, hw⟩ := point_perm e⁻¹ z
    change e.val.symm (.inl z) = .inl w at hw
    rw [← hv, Equiv.symm_apply_apply] at hw
    contradiction
  | inr b =>
    rw [hv] at hs ht
    exact ⟨b, rfl, Prod.ext hs ht⟩

private theorem restrict_preserves {Z} [Nontrivial Z] {X : Set (Z × Z)}
    (e : stabilizer (parts X)) (x y : Z) :
    (x, y) ∈ X ↔ (restrictPoints e x, restrictPoints e y) ∈ X := by
  have forward (f : stabilizer (parts X)) {a b : Z} (hab : (a, b) ∈ X) :
      (restrictPoints f a, restrictPoints f b) ∈ X := by
    obtain ⟨v, -, hv⟩ := on_edge f ⟨(a, b), hab⟩
    exact hv ▸ v.property
  refine ⟨forward e, fun h ↦ ?_⟩
  have hh := forward e⁻¹ h
  change ((restrictPoints e).symm (restrictPoints e x),
    (restrictPoints e).symm (restrictPoints e y)) ∈ X at hh
  simpa using hh

private theorem restrict_inj {Z} [Nontrivial Z] {X : Set (Z × Z)} {e f : stabilizer (parts X)}
    (h : restrictPoints e = restrictPoints f) : e = f := by
  apply Subtype.ext
  apply Equiv.ext
  rintro (z | a)
  · rw [on_point, on_point, h]
  · obtain ⟨b, hb, hb'⟩ := on_edge e a
    obtain ⟨c, hc, hc'⟩ := on_edge f a
    rw [hb, hc]
    exact congrArg Sum.inr (Subtype.ext (hb'.trans (h ▸ hc'.symm)))

private def liftPerm {Z} {X : Set (Z × Z)} (e : Equiv.Perm Z)
    (h : ∀ x y, (x, y) ∈ X ↔ (e x, e y) ∈ X) : stabilizer (parts X) := by
  let ee : Equiv.Perm X :=
    { toFun := fun a ↦ ⟨(e a.val.1, e a.val.2), (h _ _).mp a.property⟩
      invFun := fun a ↦ ⟨(e.symm a.val.1, e.symm a.val.2),
        (h _ _).mpr (by simp)⟩
      left_inv := fun a ↦ by simp
      right_inv := fun a ↦ by simp }
  let f := Equiv.sumCongr e ee
  refine ⟨f, ?_⟩
  intro k i j
  fin_cases k
  · change src i = src j ↔ src (f i) = src (f j)
    have hs t : src (f t) = e (src t) := by cases t <;> rfl
    simp [hs]
  · change dst i = dst j ↔ dst (f i) = dst (f j)
    have ht t : dst (f t) = e (dst t) := by cases t <;> rfl
    simp [ht]
  · change mark i = mark j ↔ mark (f i) = mark (f j)
    cases i <;> cases j <;> simp [f, mark]

private theorem partitions_realize (G : Type) [Group G] [Nontrivial G] :
    ∃ (I : Type) (P : Fin 3 → Setoid I), Nonempty (G ≃* stabilizer P) := by
  obtain ⟨Z, X, f, hinj, hmul, hrel, hfull⟩ :=
    ScottishBook142Wanted.everyGroupIsAutomorphismGroupOfBinaryRelation G
  have : Nontrivial Z := by
    by_contra! hs
    have : Subsingleton Z := hs
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    exact hg (hinj (Subsingleton.elim _ _))
  let φ : G →* stabilizer (parts X) := MonoidHom.mk' (fun g ↦ liftPerm (f g) (hrel g)) (by
    intro a b
    apply restrict_inj
    exact hmul a b)
  refine ⟨Inc X, parts X, ⟨MulEquiv.ofBijective φ ⟨?_, ?_⟩⟩⟩
  · intro a b h
    exact hinj (congrArg restrictPoints h)
  · intro e
    obtain ⟨a, ha⟩ := hfull _ (restrict_preserves e)
    exact ⟨a, restrict_inj ha⟩

end Partitions

noncomputable section Coordinates

private abbrev D := Localization.Away (2 : ℤ)

-- The orders of 2 modulo these primes are 3, 5 and 7. Each separating exponent is the
-- product of the other two orders, while exponent 105 gives 1 in all three residues.
private def redPrime : Fin 3 → ℕ := ![7, 31, 127]
private def period : Fin 3 → ℕ := ![35, 21, 15]

private def red (k : Fin 3) : D →+* ZMod (redPrime k) :=
  IsLocalization.Away.lift (2 : ℤ) (g := Int.castRingHom _) (by
    fin_cases k
    · exact isUnit_iff_exists_inv.mpr ⟨4, by decide⟩
    · exact isUnit_iff_exists_inv.mpr ⟨16, by decide⟩
    · exact isUnit_iff_exists_inv.mpr ⟨64, by decide⟩)

@[local simp] private theorem red_two (k : Fin 3) : red k (2 : D) = 2 := map_ofNat _ _

private theorem separate (k l : Fin 3) :
    (2 : ZMod (redPrime l)) ^ period k = 1 ↔ k ≠ l := by
  fin_cases k <;> fin_cases l <;> decide

private theorem period_all (k : Fin 3) : (2 : ZMod (redPrime k)) ^ 105 = 1 := by
  fin_cases k <;> decide

private def twoD : Dˣ := (IsLocalization.Away.algebraMap_isUnit (S := D) (2 : ℤ)).unit

private theorem twoD_val : (twoD : D) = 2 := by
  simp [twoD]

private def dyadicToRat : D →+* ℚ :=
  IsLocalization.Away.lift (2 : ℤ) (g := Int.castRingHom _) (by norm_num)

private instance dyadicCharZero : CharZero D := dyadicToRat.charZero
private instance dyadicIsDomain : IsDomain D := NoZeroDivisors.to_isDomain _

variable {I : Type} (P : Fin 3 → Setoid I)

private def compat (f : I → D) : Prop :=
  ∀ k i j, (P k).r i j → red k (f i) = red k (f j)

private def compatible : Subring (I → D) where
  carrier := {f | compat P f}
  zero_mem' := fun _ _ _ _ ↦ rfl
  one_mem' := fun _ _ _ _ ↦ rfl
  add_mem' {a b} ha hb k i j hij := by
    change red k (a i + b i) = red k (a j + b j)
    rw [map_add, map_add, ha k i j hij, hb k i j hij]
  mul_mem' {a b} ha hb k i j hij := by
    change red k (a i * b i) = red k (a j * b j)
    rw [map_mul, map_mul, ha k i j hij, hb k i j hij]
  neg_mem' {a} ha k i j hij := by
    change red k (-a i) = red k (-a j)
    rw [map_neg, map_neg, ha k i j hij]

private def generators : Set (I → D) :=
  Set.range (fun u : (compatible P)ˣ ↦ ((u : compatible P) : I → D))

-- Taking the subring generated by the compatible units lets us recover its multiplication
-- from the action of the units on its additive group.
private def coordRing := Subring.closure (generators P)
private abbrev CoordRing := ↥(coordRing P)

private theorem coord_compat (x : CoordRing P) : compat P x.val :=
  (Subring.closure_le.mpr (show generators P ⊆ compatible P by
    rintro _ ⟨u, rfl⟩
    exact (u : compatible P).property) : coordRing P ≤ compatible P) x.property

private def liftUnit (u : (compatible P)ˣ) : (CoordRing P)ˣ where
  val := ⟨_, Subring.subset_closure (Set.mem_range_self u)⟩
  inv := ⟨_, Subring.subset_closure (Set.mem_range_self u⁻¹)⟩
  val_inv := Subtype.ext (congrArg (fun x : compatible P ↦ x.val) u.val_inv)
  inv_val := Subtype.ext (congrArg (fun x : compatible P ↦ x.val) u.inv_val)

private theorem coord_generated :
    Subring.closure (Set.range (Units.val : (CoordRing P)ˣ → CoordRing P)) = ⊤ := by
  let S := Subring.closure (Set.range (Units.val : (CoordRing P)ˣ → CoordRing P))
  apply top_unique
  rintro ⟨f, hf⟩ -
  induction hf using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    exact Subring.subset_closure (Set.mem_range_self (liftUnit P u))
  | zero => exact S.zero_mem
  | one => exact S.one_mem
  | add _ _ _ _ ha hb => exact S.add_mem ha hb
  | neg _ _ ha => exact S.neg_mem ha
  | mul _ _ _ _ ha hb => exact S.mul_mem ha hb

private def makeUnit (f : I → Dˣ) (hf : compat P (fun i ↦ (f i : D))) : (compatible P)ˣ where
  val := ⟨fun i ↦ (f i : D), hf⟩
  inv := ⟨fun i ↦ (↑(f i)⁻¹ : D), fun k i j h ↦ by
    have he : Units.map (red k).toMonoidHom (f i) = Units.map (red k).toMonoidHom (f j) :=
      Units.ext (hf k i j h)
    exact congrArg (fun u : (ZMod (redPrime k))ˣ ↦ (↑u⁻¹ : ZMod (redPrime k))) he⟩
  val_inv := Subtype.ext (funext fun i ↦ (f i).val_inv)
  inv_val := Subtype.ext (funext fun i ↦ (f i).inv_val)

private def twoCoord : (CoordRing P)ˣ := liftUnit P (makeUnit P (fun _ ↦ twoD) (fun _ _ _ _ ↦ rfl))

private theorem twoCoord_val : (twoCoord P : CoordRing P) = 2 :=
  Subtype.ext (funext fun _ ↦ twoD_val)

private def cutVal : ℕ := 2 ^ 105 - 1
private theorem cutVal_ne : cutVal ≠ 0 := by decide
private theorem cut_ne : (cutVal : D) ≠ 0 := by exact_mod_cast (by decide : cutVal ≠ 0)

-- The function equal to 2 ^ 105 on one coordinate and 1 elsewhere is a compatible unit.
-- Subtracting 1 singles out that coordinate even when the index type is infinite.
private def cut (i : I) : CoordRing P := by
  classical
  let f (j : I) : Dˣ := if j = i then twoD ^ 105 else 1
  have hf : compat P (fun j ↦ (f j : D)) := by
    have h k j : red k (f j : D) = 1 := by
      simp only [f]
      split <;> simp [twoD_val, period_all]
    intro k j l _
    rw [h, h]
  exact (liftUnit P (makeUnit P f hf) : CoordRing P) - 1

open Classical in
private theorem cut_apply (i j : I) :
    (cut P i).val j = if j = i then (cutVal : D) else 0 := by
  change (↑(if j = i then twoD ^ 105 else 1) : D) - 1 = _
  by_cases h : j = i <;> norm_num [h, twoD_val, cutVal]

private def ev (i : I) : CoordRing P →+* D := (Pi.evalRingHom _ i).comp (coordRing P).subtype

private theorem ev_ext {a b : CoordRing P} (h : ∀ i, ev P i a = ev P i b) : a = b :=
  Subtype.ext (funext h)

open Classical in
private theorem ev_cut (i j : I) : ev P j (cut P i) = if j = i then (cutVal : D) else 0 :=
  cut_apply P i j

private theorem cut_inj : Function.Injective (cut P) := by
  classical
  intro i j h
  by_contra hn
  have := congrArg (ev P i) h
  simp [ev_cut, hn, cutVal_ne] at this

private theorem cut_square (i : I) : cut P i * cut P i = (cutVal : CoordRing P) * cut P i := by
  classical
  apply ev_ext
  intro j
  by_cases h : j = i <;> simp [ev_cut, h]

private theorem cut_nonzero (i : I) : cut P i ≠ 0 := by
  intro h
  have := congrArg (ev P i) h
  simp [ev_cut, cutVal_ne] at this

-- A nonzero entry of the image of a cut equals the same scalar as the original cut.
-- Pulling the cut at that entry back through the inverse rules out any other entries.
private theorem permutes_cuts (F : RingAut (CoordRing P)) (i : I) :
    ∃ j, F (cut P i) = cut P j := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, ev P j (F (cut P i)) ≠ 0 := by
    by_contra! h
    exact cut_nonzero P i (F.injective ((ev_ext P fun j ↦ (h j).trans (map_zero _).symm).trans
      F.map_zero.symm))
  have sq (H : RingAut (CoordRing P)) (l m : I) :
      ev P m (H (cut P l)) * ev P m (H (cut P l)) =
        (cutVal : D) * ev P m (H (cut P l)) := by
    simpa only [map_mul, map_natCast] using congrArg (fun a ↦ ev P m (H a)) (cut_square P l)
  have hv := mul_right_cancel₀ hj (sq F i j)
  have hm : F (cut P i) * cut P j = (cutVal : CoordRing P) * cut P j := by
    apply ev_ext P
    intro k
    by_cases h : k = j <;> simp [ev_cut, h, hv]
  have hpre := congrArg F.symm hm
  simp only [map_mul, map_natCast, RingEquiv.symm_apply_apply] at hpre
  have hoff (k : I) (hk : k ≠ i) : ev P k (F.symm (cut P j)) = 0 := by
    have h := congrArg (ev P k) hpre
    simpa [ev_cut, hk, cutVal_ne] using h.symm
  have hi : ev P i (F.symm (cut P j)) ≠ 0 := by
    intro hi
    apply cut_nonzero P j
    apply F.symm.injective
    apply ev_ext P
    intro k
    by_cases hk : k = i <;> simp [hk, hi, hoff k]
  refine ⟨j, (F.eq_symm_apply.mp ?_)⟩
  apply ev_ext P
  intro k
  by_cases hk : k = i
  · simp [hk, ev_cut, mul_right_cancel₀ hi (sq F.symm j i)]
  · simp [hk, ev_cut, hoff k hk]

private def onIndex (F : RingAut (CoordRing P)) : Equiv.Perm I where
  toFun i := (permutes_cuts P F i).choose
  invFun i := (permutes_cuts P F.symm i).choose
  left_inv i := by
    apply cut_inj P
    rw [← (permutes_cuts P F.symm _).choose_spec, ← (permutes_cuts P F i).choose_spec,
      RingEquiv.symm_apply_apply]
  right_inv i := by
    apply cut_inj P
    rw [← (permutes_cuts P F _).choose_spec, ← (permutes_cuts P F.symm i).choose_spec,
      RingEquiv.apply_symm_apply]

private theorem image_cut (F : RingAut (CoordRing P)) (i : I) :
    F (cut P i) = cut P (onIndex P F i) := (permutes_cuts P F i).choose_spec

-- Clear the power-of-two denominator of the value at i, then transport the resulting
-- equality supported on the single coordinate through the ring automorphism.
private theorem eval_image (F : RingAut (CoordRing P)) (i : I) (a : CoordRing P) :
    ev P (onIndex P F i) (F a) = ev P i a := by
  classical
  obtain ⟨n, m, h⟩ := IsLocalization.Away.surj (2 : ℤ) (ev P i a)
  have h' : ev P i a * 2 ^ n = (m : D) := by simpa using h
  have hh : a * cut P i * 2 ^ n = (m : CoordRing P) * cut P i := by
    apply ev_ext P
    intro j
    by_cases hj : j = i
    · subst j
      simp only [map_mul, map_pow, map_ofNat, map_intCast, ev_cut, ite_true]
      rw [mul_right_comm, h']
    · simp [ev_cut, hj]
  have he := congrArg (fun b ↦ ev P (onIndex P F i) (F b)) hh
  simp only [map_mul, map_pow, map_ofNat, map_intCast, image_cut, ev_cut, ite_true] at he
  rw [mul_right_comm, ← h'] at he
  exact mul_right_cancel₀ (pow_ne_zero n (by norm_num)) (mul_right_cancel₀ cut_ne he)

-- A suitable power of 2 on the class of i separates it from any other class of P k
-- without changing the reductions for the other two partitions.
private theorem detects (k : Fin 3) (i j : I) : (P k).r i j ↔
    ∀ a : CoordRing P, red k (ev P i a) = red k (ev P j a) := by
  classical
  refine ⟨fun h a ↦ coord_compat P a k i j h, fun h ↦ ?_⟩
  by_contra hij
  let f (x : I) : Dˣ := if (P k).r i x then twoD ^ (period k) else 1
  have hf : compat P (fun x ↦ (f x : D)) := by
    intro l x y hxy
    by_cases hkl : k = l
    · subst l
      have hiff : (P k).r i x ↔ (P k).r i y :=
        ⟨fun h ↦ (P k).trans h hxy, fun h ↦ (P k).trans h ((P k).symm hxy)⟩
      simp only [f, hiff]
    · have hv t : red l (f t : D) = 1 := by
        simp only [f]
        split <;> simp [twoD_val, (separate k l).mpr hkl]
      rw [hv, hv]
  have he := h (liftUnit P (makeUnit P f hf) : CoordRing P)
  change red k (f i : D) = red k (f j : D) at he
  simp [f, hij, twoD_val, separate] at he

private def indexAut (F : RingAut (CoordRing P)) : stabilizer P := by
  refine ⟨onIndex P F, ?_⟩
  intro k i j
  rw [detects P, detects P]
  constructor
  · intro h a
    simpa only [← eval_image P F i (F.symm a), ← eval_image P F j (F.symm a),
      RingEquiv.apply_symm_apply] using h (F.symm a)
  · intro h a
    simpa only [eval_image] using h (F a)

private def permFun (e : stabilizer P) (f : I → D) : I → D := f ∘ e.val.symm

private theorem perm_mem (e : stabilizer P) {f : I → D} (hf : f ∈ coordRing P) :
    permFun P e f ∈ coordRing P := by
  induction hf using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    let g (i : I) := Units.map ((Pi.evalRingHom _ (e.val.symm i)).comp
      (compatible P).subtype).toMonoidHom u
    have hg : compat P (fun i ↦ (g i : D)) :=
      fun k i j hij ↦ (u : compatible P).property k _ _ ((e⁻¹).property k i j |>.mp hij)
    exact Subring.subset_closure ⟨makeUnit P g hg, rfl⟩
  | zero => exact (coordRing P).zero_mem
  | one => exact (coordRing P).one_mem
  | add _ _ _ _ ha hb => exact (coordRing P).add_mem ha hb
  | neg _ _ ha => exact (coordRing P).neg_mem ha
  | mul _ _ _ _ ha hb => exact (coordRing P).mul_mem ha hb

private def fromIndex (e : stabilizer P) : RingAut (CoordRing P) where
  toFun x := ⟨_, perm_mem P e x.property⟩
  invFun x := ⟨_, perm_mem P e⁻¹ x.property⟩
  left_inv x := by
    apply ev_ext P
    intro i
    exact congrArg x.val (e.val.symm_apply_apply i)
  right_inv x := by
    apply ev_ext P
    intro i
    exact congrArg x.val (e.val.apply_symm_apply i)
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private def permRingEquiv : stabilizer P ≃* RingAut (CoordRing P) where
  toFun := fromIndex P
  invFun := indexAut P
  left_inv e := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply cut_inj P
    rw [← show (onIndex P (fromIndex P e)) i = (indexAut P (fromIndex P e)).val i from rfl,
      ← image_cut]
    apply ev_ext P
    intro j
    change ev P (e.val.symm j) (cut P i) = _
    classical
    by_cases h : j = e.val i
    · simp [ev_cut, h]
    · have hn : e.val.symm j ≠ i := fun he ↦ h (e.val.symm_apply_eq.mp he)
      simp [ev_cut, hn, h]
  right_inv F := by
    apply RingEquiv.ext
    intro a
    apply ev_ext P
    intro j
    obtain ⟨i, rfl⟩ := (onIndex P F).surjective j
    change ev P ((onIndex P F).symm (onIndex P F i)) a = _
    rw [Equiv.symm_apply_apply, eval_image]
  map_mul' _ _ := rfl

end Coordinates

section Affine

open scoped commutatorElement

variable {R : Type} [CommRing R]

private def action (R : Type) [CommRing R] : Rˣ →* MulAut (Multiplicative R) where
  toFun u := AddEquiv.toMultiplicative
    { toFun := fun x ↦ (u : R) * x
      invFun := fun x ↦ (↑u⁻¹ : R) * x
      left_inv := fun x ↦ by simp [← mul_assoc]
      right_inv := fun x ↦ by simp [← mul_assoc]
      map_add' := fun x y ↦ mul_add _ _ _ }
  map_one' := by ext x; exact one_mul _
  map_mul' u v := by ext x; exact mul_assoc _ _ _

private abbrev AffineGroup (R : Type) [CommRing R] := SemidirectProduct _ _ (action R)

private abbrev tr (r : R) : AffineGroup R := SemidirectProduct.inl (Multiplicative.ofAdd r)
private abbrev dil (u : Rˣ) : AffineGroup R := SemidirectProduct.inr u

private theorem split (x : AffineGroup R) : tr x.left.toAdd * dil x.right = x :=
  SemidirectProduct.inl_left_mul_inr_right _

private theorem prod_coords (x y : AffineGroup R) : (x * y).left.toAdd =
    x.left.toAdd + (x.right : R) * y.left.toAdd := rfl

private theorem tr_add (r s : R) : tr (r + s) = tr r * tr s :=
  SemidirectProduct.inl.map_mul _ _

private theorem conj_tr (g : AffineGroup R) (a : R) :
    g * tr a * g⁻¹ = tr ((g.right : R) * a) := by
  apply SemidirectProduct.ext
  · change g.left.toAdd + (g.right : R) * a + (↑(g.right * 1) : R) *
        ((↑g.right⁻¹ : R) * -g.left.toAdd) = (g.right : R) * a
    simp [← mul_assoc, add_comm]
  · simp

-- Commuting with the dilation by 2 gives every translation as a commutator.
private theorem comm_tr (d : Rˣ) (hd : (d : R) = 2) (a : R) :
    ⁅dil d, tr a⁆ = tr a := by
  rw [commutatorElement_def, conj_tr, show (dil d).right = d from rfl, hd]
  rw [two_mul, tr_add, mul_inv_cancel_right]

private theorem comm_right {g : AffineGroup R} (hg : g ∈ commutator (AffineGroup R)) :
    g.right = 1 :=
  Group.Abelianization.commutator_le_ker (SemidirectProduct.rightHom (φ := action R)) hg

private theorem affine_metabelian : Subgroup.derivedSeries (AffineGroup R) 2 = ⊥ := by
  apply le_antisymm _ bot_le
  apply Subgroup.commutator_le.mpr
  intro a ha b hb
  have ha' := comm_right ha
  have hb' := comm_right hb
  apply Subgroup.mem_bot.mpr
  apply commutatorElement_eq_one_iff_mul_comm.mpr
  apply SemidirectProduct.ext
  · change a.left.toAdd + (a.right : R) * b.left.toAdd =
        b.left.toAdd + (b.right : R) * a.left.toAdd
    simp [ha', hb', add_comm]
  · exact mul_comm _ _

private theorem affine_center (d : Rˣ) (hd : (d : R) = 2) :
    Subgroup.center (AffineGroup R) = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  have h := Subgroup.mem_center_iff.mp hg
  have h₁ := congrArg (fun x : AffineGroup R ↦ x.left.toAdd) (h (tr 1))
  have h₂ := congrArg (fun x : AffineGroup R ↦ x.left.toAdd) (h (dil d))
  change 1 + 1 * g.left.toAdd = g.left.toAdd + (g.right : R) * 1 at h₁
  change 0 + (d : R) * g.left.toAdd = g.left.toAdd + (g.right : R) * 0 at h₂
  simp only [one_mul, mul_one, add_comm (1 : R), add_right_inj] at h₁
  simp only [hd, two_mul, zero_add, mul_zero, add_zero, add_eq_left] at h₂
  exact SemidirectProduct.ext (congrArg Multiplicative.ofAdd h₂) (Units.ext h₁.symm)

private theorem image_tr_right (F : MulAut (AffineGroup R)) (d : Rˣ) (hd : (d : R) = 2) (a : R) :
    (F (tr a)).right = 1 := by
  rw [← comm_tr d hd a, map_commutatorElement]
  exact comm_right (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

private def res (F : MulAut (AffineGroup R)) (x : R) : R := (F (tr x)).left.toAdd

private theorem image_tr (F : MulAut (AffineGroup R)) (d : Rˣ) (hd : (d : R) = 2) (a : R) :
    F (tr a) = tr (res F a) :=
  SemidirectProduct.ext rfl (image_tr_right F d hd a)

private def additivePart (F : MulAut (AffineGroup R)) (d : Rˣ) (hd : (d : R) = 2) : R ≃+ R where
  toFun := res F
  invFun := res F.symm
  left_inv x := by
    change (F.symm (tr (res F x))).left.toAdd = x
    rw [← image_tr F d hd, MulEquiv.symm_apply_apply]
    rfl
  right_inv x := by
    change (F (tr (res F.symm x))).left.toAdd = x
    rw [← image_tr F.symm d hd, MulEquiv.apply_symm_apply]
    rfl
  map_add' x y := by
    rw [res, tr_add, map_mul, prod_coords, image_tr_right F d hd]
    simp [res]

private abbrev linPart (F : MulAut (AffineGroup R)) (u : Rˣ) : Rˣ := (F (dil u)).right

private theorem semilinear_unit (F : MulAut (AffineGroup R)) (d : Rˣ) (hd : (d : R) = 2)
    (u : Rˣ) (x : R) : res F (u * x) = (linPart F u : R) * res F x := by
  have h := congrArg F (conj_tr (dil u) x)
  rw [map_mul, map_mul, map_inv, image_tr F d hd x, conj_tr] at h
  exact congrArg (fun g : AffineGroup R ↦ g.left.toAdd) h.symm

-- Conjugating multiplication by a unit through the additive part gives multiplication
-- by another unit. This extends to every scalar because the units generate the ring.
private def scalar (A : R ≃+ R) (a : R) : R := A (a * A.symm 1)

private theorem scalar_unique (A : R ≃+ R) {a b : R}
    (h : ∀ x, A (a * x) = b * A x) : scalar A a = b := by
  simpa [scalar] using h (A.symm 1)

private theorem semilinear (F : MulAut (AffineGroup R)) (d : Rˣ) (hd : (d : R) = 2)
    (hgen : Subring.closure (Set.range (Units.val : Rˣ → R)) = ⊤) (a x : R) :
    let A := additivePart F d hd
    A (a * x) = scalar A a * A x := by
  let A := additivePart F d hd
  let S : Subring R :=
    { carrier := {a | ∃ b, ∀ x, A (a * x) = b * A x}
      one_mem' := ⟨1, fun x ↦ by simp⟩
      zero_mem' := ⟨0, fun x ↦ by simp⟩
      neg_mem' := by
        rintro a ⟨b, hb⟩
        exact ⟨-b, fun x ↦ by simp [neg_mul, hb]⟩
      add_mem' := by
        rintro a c ⟨b, hb⟩ ⟨d, hd⟩
        exact ⟨b + d, fun x ↦ by simp [add_mul, hb, hd]⟩
      mul_mem' := by
        rintro a c ⟨b, hb⟩ ⟨d, hd⟩
        exact ⟨b * d, fun x ↦ by simp [mul_assoc, hb, hd]⟩ }
  have hS : Subring.closure (Set.range (Units.val : Rˣ → R)) ≤ S := by
    apply Subring.closure_le.mpr
    rintro _ ⟨u, rfl⟩
    exact ⟨_, semilinear_unit F d hd u⟩
  obtain ⟨b, hb⟩ := (show a ∈ S from hS (hgen ▸ Subring.mem_top a))
  exact (hb x).trans (by rw [scalar_unique A hb])

private def ringPart (F : MulAut (AffineGroup R)) (d : Rˣ) (hd : (d : R) = 2)
    (hgen : Subring.closure (Set.range (Units.val : Rˣ → R)) = ⊤) : RingAut R := by
  let A := additivePart F d hd
  have hs := semilinear F d hd hgen
  have hinv (E : MulAut (AffineGroup R)) (a : R) :
      let B := additivePart E d hd
      scalar B.symm (scalar B a) = a := by
    dsimp only
    apply scalar_unique
    intro x
    apply (additivePart E d hd).injective
    rw [AddEquiv.apply_symm_apply, semilinear E d hd hgen, AddEquiv.apply_symm_apply]
  exact
    { toFun := scalar A
      invFun := scalar A.symm
      left_inv := hinv F
      right_inv := hinv F.symm
      map_mul' a b := scalar_unique A (fun x ↦ by rw [mul_assoc, hs, hs, mul_assoc])
      map_add' a b := by simp [scalar, add_mul] }

private theorem res_comp (F H : MulAut (AffineGroup R)) (d : Rˣ) (hd : (d : R) = 2) (x : R) :
    res (F * H) x = res F (res H x) := by
  change (F (H (tr x))).left.toAdd = _
  rw [image_tr H d hd]
  rfl

private def ringProj (d : Rˣ) (hd : (d : R) = 2)
    (hgen : Subring.closure (Set.range (Units.val : Rˣ → R)) = ⊤) :
    MulAut (AffineGroup R) →* RingAut R where
  toFun F := ringPart F d hd hgen
  map_one' := by
    ext x
    change x * 1 = x
    exact mul_one _
  map_mul' F H := by
    ext a
    apply scalar_unique (additivePart (F * H) d hd)
    intro x
    change res (F * H) (a * x) = _ * res (F * H) x
    rw [res_comp F H d hd, res_comp F H d hd]
    change (additivePart F d hd) (additivePart H d hd (a * x)) = _
    rw [semilinear H d hd hgen, semilinear F d hd hgen]
    rfl

private def fromRing (e : RingAut R) : MulAut (AffineGroup R) :=
  SemidirectProduct.congr (AddEquiv.toMultiplicative e.toAddEquiv)
    (Units.mapEquiv e.toMulEquiv) (fun u ↦ by
      ext x
      exact e.map_mul (u : R) x.toAdd)

private theorem ringProj_surj (d : Rˣ) (hd : (d : R) = 2)
    (hgen : Subring.closure (Set.range (Units.val : Rˣ → R)) = ⊤) :
    Function.Surjective (ringProj d hd hgen) := by
  intro e
  refine ⟨fromRing e, ?_⟩
  ext a
  apply scalar_unique
  exact fun x ↦ e.map_mul a x

private theorem res_of_ker (F : MulAut (AffineGroup R)) (d : Rˣ) (hd : (d : R) = 2)
    (hgen : Subring.closure (Set.range (Units.val : Rˣ → R)) = ⊤)
    (h : ringProj d hd hgen F = 1) (a : R) : res F a = a * res F 1 := by
  have ha := DFunLike.congr_fun h a
  change scalar (additivePart F d hd) a = a at ha
  change additivePart F d hd a = a * additivePart F d hd 1
  simpa only [ha, mul_one] using semilinear F d hd hgen a 1

-- In the kernel the additive part is multiplication by a unit. The image of the dilation
-- by 2 then determines the translation needed to realize the entire automorphism by conjugation.
private theorem ringProj_ker (d : Rˣ) (hd : (d : R) = 2)
    (hgen : Subring.closure (Set.range (Units.val : Rˣ → R)) = ⊤) :
    (ringProj d hd hgen).ker = (MulAut.conj (G := AffineGroup R)).range := by
  ext F
  constructor
  · intro h
    change ringProj d hd hgen F = 1 at h
    have ht := res_of_ker F d hd hgen h
    obtain ⟨y, hy⟩ := (additivePart F d hd).surjective 1
    change res F y = 1 at hy
    rw [ht y] at hy
    let u : Rˣ := ⟨res F 1, y, (mul_comm _ _).trans hy, hy⟩
    have hlin (v : Rˣ) : linPart F v = v := by
      apply Units.ext
      have hv := semilinear_unit F d hd v 1
      rw [mul_one, ht (v : R)] at hv
      exact u.isUnit.mul_right_cancel hv.symm
    let t := (F (dil d)).left.toAdd
    have ht' (v : Rˣ) : (F (dil v)).left.toAdd = (v : R) * t - t := by
      have hcomm : dil d * dil v = dil v * dil d := by
        rw [← SemidirectProduct.inr.map_mul, mul_comm, SemidirectProduct.inr.map_mul]
      have hh := congrArg (fun z : AffineGroup R ↦ (F z).left.toAdd) hcomm
      simp only [map_mul, prod_coords] at hh
      change t + (linPart F d : R) * _ = _ + (linPart F v : R) * t at hh
      rw [hlin, hlin, hd, two_mul] at hh
      linear_combination hh
    let g : AffineGroup R := ⟨Multiplicative.ofAdd (-t), u⟩
    refine ⟨g, ?_⟩
    apply MulEquiv.ext
    intro z
    rw [← split z, map_mul, map_mul]
    congr 1
    · rw [MulAut.conj_apply, conj_tr, image_tr F d hd, ht]
      congr 1
      exact mul_comm _ _
    · rw [MulAut.conj_apply]
      apply SemidirectProduct.ext
      · apply Multiplicative.toAdd.injective
        change -t + (u : R) * 0 + (↑(u * z.right) : R) *
            ((↑u⁻¹ : R) * -(-t)) = _
        rw [ht' z.right]
        simp [mul_comm, mul_assoc, sub_eq_add_neg, add_comm]
      · change u * z.right * u⁻¹ = linPart F z.right
        simp [hlin, mul_comm, mul_assoc]
  · rintro ⟨g, rfl⟩
    apply MonoidHom.mem_ker.mpr
    ext a
    apply scalar_unique (additivePart (MulAut.conj g) d hd)
    intro x
    change res (MulAut.conj g) (a * x) = a * res (MulAut.conj g) x
    simp only [res, MulAut.conj_apply, conj_tr]
    change _ * (a * x) = a * (_ * x)
    ring

end Affine

/--
**Every group is the outer automorphism group of a centreless metabelian group.** For every group
$G$ there is a metabelian group $M$ (one whose second derived subgroup $M''$ is trivial) with
trivial centre such that the outer automorphism group
$\operatorname{Out}(M) = \operatorname{Aut}(M)/\operatorname{Inn}(M)$ is isomorphic to $G$. This
answers Kourovka Problem 11.26 (Göbel) in the negative (Göbel and Paras).

Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.26 (R. Göbel); resolution: R.
Göbel and A. Paras, J. Pure Appl. Algebra 149, no. 3 (2000), 251-266, Kourovka Archive, Problem
11.26: "No, given any group `G` there is a metabelian group `M` with trivial center such that `Out M
≅ G`", https://arxiv.org/abs/1401.0300v49.
-/
theorem groupNotOuterAutOfMetabelian_refuted : ¬ groupNotOuterAutOfMetabelian := by
  rintro ⟨G, inst, hG⟩
  cases subsingleton_or_nontrivial G with
  | inl h =>
    have : Subsingleton (MulAut G) := ⟨fun f g ↦ MulEquiv.ext fun x ↦ Subsingleton.elim _ _⟩
    exact hG G (Subsingleton.elim _ _) (Subsingleton.elim _ _)
      ⟨1, fun x ↦ ⟨1, Subsingleton.elim _ _⟩, Subsingleton.elim _ _⟩
  | inr h =>
    obtain ⟨I, P, ⟨e⟩⟩ := partitions_realize G
    let d := twoCoord P
    have hd := twoCoord_val P
    have hgen := coord_generated P
    let π := ringProj d hd hgen
    let iso := (e.trans (permRingEquiv P)).symm
    apply hG (AffineGroup (CoordRing P)) affine_metabelian (affine_center d hd)
    refine ⟨iso.toMonoidHom.comp π, iso.surjective.comp (ringProj_surj d hd hgen), ?_⟩
    rw [← ringProj_ker d hd hgen]
    ext F
    change iso (π F) = 1 ↔ π F = 1
    exact iso.map_eq_one_iff

end MathlibExt.GroupTheory.OuterAutomorphismMetabelianKourovka11Problem26Wanted
