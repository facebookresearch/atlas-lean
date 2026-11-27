/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Group.Shrink
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.Logic.Small.Basic
import Mathlib.Tactic.Ring

/-!
# Nilpotent extensions that split at every prime need not split (Kourovka 12.93)

Kourovka Notebook, Problem 12.93 (P. Hilton): Let `N ↣ G ↠ Q` be an extension of nilpotent groups,
with `Q` finitely generated, which splits at every prime. Does the extension split? This is known to
be true if `N` is finite or commutative. Archive of Solved Problems: No, not always (K. Lorensen,
Math. Proc. Cambridge Philos. Soc. 123, no. 2 (1998), 213-215).

We construct a class-two group mapping onto the rank-two integer lattice. Twice the standard
basis and three times the standard basis admit commuting lifts, but the basis itself does not.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.93 (P.
Hilton). UnsolvedMath record UM-00700910 (`KOU-12.93`), dataset ulamai/UnsolvedMath v1.8.0.

Reading: 'splits at every prime' is read as in Hilton's localization theory and in Lorensen's paper:
for every prime `p` the `p`-localized extension `N_p ↣ G_p ↠ Q_p` splits. The `p`-localization of a
nilpotent group is given by its universal property (Hilton, Mislin and Roitberg): a homomorphism to
a nilpotent `p`-local group (`x ↦ xⁿ` bijective for every `n` coprime to `p`) through which every
homomorphism to a nilpotent `p`-local group factors uniquely. The localized extension splits iff the
localized quotient map `π_p : G_p →* Q_p` has a homomorphic section; since localizations are unique
up to unique isomorphism, this does not depend on the chosen localizations. An extension splits iff
its quotient map has a homomorphic section. The answer is stated as the negation of the universal
claim, with groups in `Type`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.NilpotentExtensionSplitAtPrimesKourovka12Problem93Wanted

/-- **$p$-local groups.** Let $p$ be a natural number. A group $H$ is $p$-local when, for every
natural number $n$ coprime to $p$, the map $x \mapsto x^n$ is a bijection of $H$.

This is the notion of a $P$-local group of Hilton, Mislin and Roitberg, for $P$ the set whose only
element is $p$. -/
def IsPLocal (p : ℕ) (H : Type*) [Group H] : Prop :=
  ∀ n : ℕ, Nat.Coprime n p → Function.Bijective fun x : H => x ^ n

/-- **$p$-localization of a group.** Let $p$ be a natural number. A homomorphism of groups
$e \colon G \to L$ is a $p$-localization when $L$ is nilpotent and $p$-local, and every
homomorphism $f$ from $G$ to a nilpotent $p$-local group $H$ factors uniquely through $e$: there is
exactly one homomorphism $g \colon L \to H$ with $g \circ e = f$. -/
def IsPLocalization (p : ℕ) {G L : Type} [Group G] [Group L] (e : G →* L) : Prop :=
  Group.IsNilpotent L ∧ IsPLocal p L ∧
    ∀ (H : Type) [Group H], Group.IsNilpotent H → IsPLocal p H →
      ∀ f : G →* H, ∃! g : L →* H, g.comp e = f

/-- **Splitting at a prime.** Let $p$ be a natural number and $\pi \colon G \to Q$ a homomorphism
of groups (in the intended use, the quotient map of an extension). Then $\pi$ splits at $p$ when
there exist $p$-localizations $e_G \colon G \to G_p$ and $e_Q \colon Q \to Q_p$ and homomorphisms
$\pi_p \colon G_p \to Q_p$ and $s \colon Q_p \to G_p$ with $\pi_p \circ e_G = e_Q \circ \pi$ and
$\pi_p \circ s = \mathrm{id}_{Q_p}$; that is, the localized quotient map $\pi_p$ has a homomorphic
section.

Since $Q_p$ is nilpotent and $p$-local, $\pi_p$ is the unique homomorphism with
$\pi_p \circ e_G = e_Q \circ \pi$; since localizations are unique up to unique isomorphism, the
condition does not depend on the chosen localizations. -/
def SplitsAtPrime (p : ℕ) {G Q : Type} [Group G] [Group Q] (π : G →* Q) : Prop :=
  ∃ (Gp Qp : Type) (_ : Group Gp) (_ : Group Qp) (eG : G →* Gp) (eQ : Q →* Qp)
    (πp : Gp →* Qp) (s : Qp →* Gp), IsPLocalization p eG ∧ IsPLocalization p eQ ∧
      πp.comp eG = eQ.comp π ∧ πp.comp s = MonoidHom.id Qp

/-- **Hilton's splitting question for nilpotent extensions (Kourovka 12.93).** The proposition
that every extension of nilpotent groups with finitely generated quotient that splits at every
prime splits: for all nilpotent groups $N$, $G$ and $Q$ with $Q$ finitely generated, every
injective homomorphism $i \colon N \to G$ and every surjective homomorphism $\pi \colon G \to Q$
with $\operatorname{im} i = \ker \pi$ such that the extension splits at every prime $p$, there is
a homomorphism $s \colon Q \to G$ with $\pi \circ s = \mathrm{id}_Q$. -/
def nilpotentExtensionSplitsIfSplitsAtPrimes : Prop :=
  ∀ (N G Q : Type) [Group N] [Group G] [Group Q], Group.IsNilpotent N → Group.IsNilpotent G →
    Group.IsNilpotent Q → Group.FG Q → ∀ (i : N →* G) (π : G →* Q),
      Function.Injective i → Function.Surjective π → i.range = π.ker →
      (∀ p : ℕ, p.Prime → SplitsAtPrime p π) → ∃ s : Q →* G, π.comp s = MonoidHom.id Q

open scoped commutatorElement

/- We first construct the localizations needed for groups of class at most two.
Take the group of expressions in elements of the original group, allowing products,
inverses, and the specified roots, identified if all evaluations agree. -/
private inductive Expression (p : ℕ) (G : Type)
  | gen (x : G)
  | mul (a b : Expression p G)
  | inv (a : Expression p G)
  | root (n : ℕ) (hn : n.Coprime p) (a : Expression p G)

private structure Evaluation (p : ℕ) (G : Type) [Group G] where
  carrier : Type
  [inst : Group carrier]
  isLocal : IsPLocal p carrier
  hom : G →* carrier

attribute [local instance] Evaluation.inst

private noncomputable def eval {p : ℕ} {G : Type} [Group G] (t : Evaluation p G) :
    Expression p G → t.carrier
  | .gen x => t.hom x
  | .mul a b => eval t a * eval t b
  | .inv a => (eval t a)⁻¹
  | .root n hn a => ((t.isLocal n hn).surjective (eval t a)).choose

private noncomputable abbrev evaluations {p : ℕ} {G : Type} [Group G] (a : Expression p G) :=
  fun t : Evaluation p G => eval t a

private noncomputable def expressionGroup (p : ℕ) (G : Type) [Group G] :
    Subgroup ((t : Evaluation p G) → t.carrier) where
  carrier := Set.range evaluations
  one_mem' := ⟨.gen 1, funext fun t => t.hom.map_one⟩
  mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨.mul a b, rfl⟩
  inv_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨.inv a, rfl⟩

private noncomputable def value {p : ℕ} {G : Type} [Group G] (a : Expression p G) :
    expressionGroup p G := ⟨evaluations a, a, rfl⟩

private instance smallExpressionGroup (p : ℕ) (G : Type) [Group G] :
    Small.{0} (expressionGroup p G) :=
  small_of_surjective (f := value) (fun ⟨_, a, h⟩ => ⟨a, Subtype.ext h⟩)

/-- Induction by group operations and taking roots of order coprime to the prime. -/
private def RootGenerated (p : ℕ) {G L : Type} [Group G] [Group L] (e : G →* L) : Prop :=
  ∀ P : L → Prop, (∀ x, P (e x)) → (∀ x y, P x → P y → P (x * y)) →
    (∀ x, P x → P x⁻¹) → (∀ n : ℕ, n.Coprime p → ∀ x, P (x ^ n) → P x) → ∀ x, P x

private theorem exists_localHull (p : ℕ) (G : Type) [Group G] :
    ∃ (L : Type) (_ : Group L) (e : G →* L), IsPLocal p L ∧ RootGenerated p e ∧
      ∀ (H : Type) [Group H], IsPLocal p H → ∀ f : G →* H, ∃ g : L →* H, g.comp e = f := by
  classical
  let L := Shrink.{0} (expressionGroup p G)
  let E : L ≃* expressionGroup p G := Shrink.mulEquiv
  let v (a : Expression p G) := E.symm (value a)
  let e₀ : G →* expressionGroup p G :=
    { toFun := fun x => value (.gen x)
      map_one' := Subtype.ext (funext fun t => t.hom.map_one)
      map_mul' := fun x y => Subtype.ext (funext fun t => t.hom.map_mul x y) }
  let e := E.symm.toMonoidHom.comp e₀
  have hv (x : L) : ∃ a, v a = x := by
    obtain ⟨a, ha⟩ := (E x).property
    exact ⟨a, E.symm_apply_eq.mpr (Subtype.ext ha)⟩
  have hr (n : ℕ) (hn : n.Coprime p) (a : Expression p G) :
      v (.root n hn a) ^ n = v a := by
    rw [← map_pow]
    apply congrArg E.symm
    exact Subtype.ext (funext fun t => ((t.isLocal n hn).surjective (eval t a)).choose_spec)
  refine ⟨L, inferInstance, e, ?_, ?_, ?_⟩
  · intro n hn
    refine ⟨fun {x y} h => E.injective (Subtype.ext (funext fun t => ?_)), fun x => ?_⟩
    · apply (t.isLocal n hn).injective
      exact congrArg (fun w : expressionGroup p G => w.val t)
        (show E x ^ n = E y ^ n by simpa only [← map_pow] using congrArg E h)
    · obtain ⟨a, rfl⟩ := hv x
      exact ⟨_, hr n hn a⟩
  · intro P hgen hmul hinv hroot x
    obtain ⟨a, rfl⟩ := hv x
    induction a with
    | gen x => exact hgen x
    | mul a b ha hb =>
      change P (E.symm (value a * value b))
      rw [map_mul]
      exact hmul _ _ ha hb
    | inv a ha =>
      change P (E.symm (value a)⁻¹)
      rw [map_inv]
      exact hinv _ ha
    | root n hn a ha => exact hroot n hn _ ((hr n hn a).symm ▸ ha)
  · intro H instH hH f
    let t : Evaluation p G := ⟨H, hH, f⟩
    let g : expressionGroup p G →* H :=
      { toFun := fun x => x.val t
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact ⟨g.comp E.toMonoidHom, MonoidHom.ext fun x => by
      change (E (E.symm (e₀ x))).val t = _
      rw [E.apply_symm_apply]
      rfl⟩

private theorem commute_of_pow {H : Type*} [Group H] {n : ℕ}
    (hn : Function.Injective fun a : H => a ^ n) {x y : H} (h : Commute x (y ^ n)) :
    Commute x y := by
  have he : MulAut.conj x y = y := hn (by
    change (MulAut.conj x y) ^ n = y ^ n
    rw [← map_pow, MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
    exact h.eq)
  exact mul_inv_eq_iff_eq_mul.mp he

/- Uniqueness of roots descends modulo the center: if the powers agree up to a central
factor, then the two elements commute, and their ratio has central power. -/
private theorem quotientCenter_pow_injective {L : Type} [Group L] {n : ℕ}
    (hn : Function.Injective fun x : L => x ^ n) :
    Function.Injective fun x : L ⧸ Subgroup.center L => x ^ n := by
  intro a b
  induction a, b using Quotient.inductionOn₂' with
  | _ x y =>
    intro h
    have hc := QuotientGroup.eq_iff_div_mem.mp
      (show (↑(x ^ n) : L ⧸ Subgroup.center L) = ↑(y ^ n) from h)
    have hcy : Commute y (x ^ n / y ^ n) := Subgroup.mem_center_iff.mp hc y
    have hy : Commute y (x ^ n) := by
      simpa only [div_mul_cancel] using hcy.mul_right ((Commute.refl y).pow_right n)
    have hxy := (commute_of_pow hn hy).symm
    apply QuotientGroup.eq_iff_div_mem.mpr
    apply Subgroup.mem_center_iff.mpr
    intro z
    apply (commute_of_pow hn (x := z) (y := x / y) ?_).eq
    rw [hxy.div_pow]
    exact Subgroup.mem_center_iff.mp hc z

private theorem rootGenerated_commute {p : ℕ} {G L H : Type} [Group G] [Group L] [Group H]
    {e : G →* L} (hg : RootGenerated p e) (f : L →* H) (z : H)
    (hi : ∀ n : ℕ, n.Coprime p → Function.Injective fun x : H => x ^ n)
    (hz : ∀ a, Commute z (f (e a))) : ∀ x, Commute z (f x) := by
  refine hg (fun x => Commute z (f x)) hz ?_ ?_ ?_
  · intro x y hx hy
    simpa only [map_mul] using hx.mul_right hy
  · intro x hx
    simpa only [map_inv] using hx.inv_right
  · intro n hn x hx
    exact commute_of_pow (hi n hn) (by simpa only [map_pow] using hx)

private theorem nilpotent_of_central_commutators {L : Type} [Group L]
    (h : ∀ x y : L, ⁅x, y⁆ ∈ Subgroup.center L) : Group.IsNilpotent L := by
  refine ⟨2, top_unique fun x _ => Subgroup.mem_upperCentralSeries_succ_iff.mpr fun y => ?_⟩
  simpa only [Subgroup.upperCentralSeries_one] using h x y

private theorem exists_localization {G : Type} [Group G] (p : ℕ)
    (hc : ∀ a b : G, ⁅a, b⁆ ∈ Subgroup.center G) :
    ∃ (L : Type) (_ : Group L) (e : G →* L), IsPLocalization p e := by
  obtain ⟨L, instL, e, hl, hg, he⟩ := exists_localHull p G
  -- First extend centrality of the original commutators through all root expressions.
  let q := QuotientGroup.mk' (Subgroup.center L)
  have central (a b : G) : e ⁅a, b⁆ ∈ Subgroup.center L := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    have h := rootGenerated_commute hg (MonoidHom.id L) (e ⁅a, b⁆)
      (fun n hn => (hl n hn).injective) (fun g =>
        (show Commute g ⁅a, b⁆ from Subgroup.mem_center_iff.mp (hc a b) g).symm.map e) x
    exact h.eq.symm
  -- Modulo the center the generators commute. Root induction extends this to the whole group.
  have hi (n : ℕ) (hn : n.Coprime p) := quotientCenter_pow_injective (hl n hn).injective
  have comm (a b : G) : Commute (q (e a)) (q (e b)) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (central a b)
  refine ⟨L, instL, e, nilpotent_of_central_commutators (fun x y => ?_), hl, ?_⟩
  · apply (QuotientGroup.eq_one_iff _).mp
    change q ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact rootGenerated_commute hg q (q x) hi
      (fun b => (rootGenerated_commute hg q (q (e b)) hi (comm b) x).symm) y
  · intro H instH _ hH f
    obtain ⟨g, hgf⟩ := he H hH f
    refine ⟨g, hgf, fun k hk => MonoidHom.ext (hg (fun x => k x = g x) ?_ ?_ ?_ ?_)⟩
    · exact fun a => DFunLike.congr_fun (hk.trans hgf.symm) a
    · intro x y hx hy
      simp only [map_mul, hx, hy]
    · intro x hx
      simp only [map_inv, hx]
    · intro n hn x hx
      exact (hH n hn).injective (by simpa only [map_pow] using hx)

/- A central extension of the lattice with coordinates (a,b,u,v). The two
bilinear cocycles are a u' and (2u-a)(3v'-b'). The quotient remembers (a,b). -/
@[ext] private structure Cover where
  a : ℤ
  b : ℤ
  u : ℤ
  v : ℤ
  c : ℤ
  d : ℤ

private def coverMul (x y : Cover) : Cover :=
  ⟨x.a + y.a, x.b + y.b, x.u + y.u, x.v + y.v,
    x.c + y.c + x.a * y.u, x.d + y.d + (2 * x.u - x.a) * (3 * y.v - y.b)⟩

private def coverInv (x : Cover) : Cover :=
  ⟨-x.a, -x.b, -x.u, -x.v, -x.c + x.a * x.u, -x.d + (2 * x.u - x.a) * (3 * x.v - x.b)⟩

private def origin : Cover := ⟨0, 0, 0, 0, 0, 0⟩

private instance coverGroup : Group Cover where
  one := origin
  mul := coverMul
  inv := coverInv
  mul_assoc x y z := by
    change coverMul (coverMul x y) z = coverMul x (coverMul y z)
    apply Cover.ext <;> dsimp only [coverMul] <;> ring
  one_mul x := by
    change coverMul origin x = x
    apply Cover.ext <;> simp [coverMul, origin]
  mul_one x := by
    change coverMul x origin = x
    apply Cover.ext <;> simp [coverMul, origin]
  inv_mul_cancel x := by
    change coverMul (coverInv x) x = origin
    apply Cover.ext <;> dsimp only [coverMul, coverInv, origin] <;> ring

private theorem cover_central (x y : Cover) : ⁅x, y⁆ ∈ Subgroup.center Cover := by
  let k := coverMul (coverMul (coverMul x y) (coverInv x)) (coverInv y)
  apply Subgroup.mem_center_iff.mpr
  intro z
  change coverMul z k = coverMul k z
  apply Cover.ext <;> dsimp only [k, coverMul, coverInv] <;> ring

private abbrev Lattice := Multiplicative ℤ × Multiplicative ℤ

private def projection : Cover →* Lattice where
  toFun x := (Multiplicative.ofAdd x.a, Multiplicative.ofAdd x.b)
  map_one' := rfl
  map_mul' _ _ := rfl

private def firstBasis : Lattice := (Multiplicative.ofAdd 1, 1)
private def secondBasis : Lattice := (1, Multiplicative.ofAdd 1)

private theorem lattice_decomposition (x : Lattice) :
    firstBasis ^ x.1.toAdd * secondBasis ^ x.2.toAdd = x := by
  ext <;> simp [firstBasis, secondBasis, ← ofAdd_zsmul]

private theorem no_section (s : Lattice →* Cover) (hs : projection.comp s = MonoidHom.id _) :
    False := by
  let x := s firstBasis
  let y := s secondBasis
  have hx := DFunLike.congr_fun hs firstBasis
  have hy := DFunLike.congr_fun hs secondBasis
  have hxa : x.a = 1 := congrArg (fun q : Lattice => q.1.toAdd) hx
  have hxb : x.b = 0 := congrArg (fun q : Lattice => q.2.toAdd) hx
  have hya : y.a = 0 := congrArg (fun q : Lattice => q.1.toAdd) hy
  have hyb : y.b = 1 := congrArg (fun q : Lattice => q.2.toAdd) hy
  have hxy : x * y = y * x := (Commute.all firstBasis secondBasis).map s
  have hc := congrArg Cover.c hxy
  change x.c + y.c + x.a * y.u = y.c + x.c + y.a * x.u at hc
  rw [hxa, hya] at hc
  have hu : y.u = 0 := by omega
  have hd := congrArg Cover.d hxy
  change x.d + y.d + (2 * x.u - x.a) * (3 * y.v - y.b) =
    y.d + x.d + (2 * y.u - y.a) * (3 * x.v - x.b) at hd
  rw [hu, hxa, hya, hyb, hxb] at hd
  have hz : (2 * x.u - 1) * (3 * y.v - 1) = 0 := by omega
  rcases mul_eq_zero.mp hz with h | h <;> omega

/- The two pairs lift multiples of the standard basis. In the first pair the
left factor of the second cocycle vanishes, in the second pair the right one does. -/
private theorem commuting_lifts (p : ℕ) (hp : p.Prime) :
    ∃ (n : ℕ) (x y : Cover), n.Coprime p ∧ Commute x y ∧
      projection x = firstBasis ^ n ∧ projection y = secondBasis ^ n := by
  by_cases h : p = 2
  · subst p
    exact ⟨3, ⟨3, 0, 0, 0, 0, 0⟩, ⟨0, 3, 0, 1, 0, 0⟩, by decide, rfl, rfl, rfl⟩
  · exact ⟨2, ⟨2, 0, 1, 0, 0, 0⟩, ⟨0, 2, 0, 0, 0, 0⟩,
      (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm h), rfl, rfl, rfl⟩

private theorem splits_projection (p : ℕ) (hp : p.Prime) : SplitsAtPrime p projection := by
  obtain ⟨L, instL, e, he⟩ := exists_localization p cover_central
  obtain ⟨Q, instQ, j, hj⟩ := exists_localization (G := Lattice) p (fun a b => by
    rw [(Commute.all a b).commutator_eq]
    exact (Subgroup.center _).one_mem)
  obtain ⟨π, hπ, _⟩ := he.2.2 Q hj.1 hj.2.1 (j.comp projection)
  obtain ⟨n, x, y, hn, hxy, hx, hy⟩ := commuting_lifts p hp
  -- Unique roots turn the commuting lifts of the two multiples into lifts of the basis.
  obtain ⟨u, hu⟩ := (he.2.1 n hn).surjective (e x)
  obtain ⟨v, hv⟩ := (he.2.1 n hn).surjective (e y)
  change u ^ n = e x at hu
  change v ^ n = e y at hv
  have hcomm : Commute u v := by
    have h : Commute (u ^ n) (v ^ n) := by rw [hu, hv]; exact hxy.map e
    exact (commute_of_pow (he.2.1 n hn).injective
      (commute_of_pow (he.2.1 n hn).injective h).symm).symm
  have image {w : L} {g : Cover} {q : Lattice} (hw : w ^ n = e g)
      (hq : projection g = q ^ n) : π w = j q := by
    apply (hj.2.1 n hn).injective
    calc
      π w ^ n = π (e g) := by rw [← map_pow, hw]
      _ = j (projection g) := DFunLike.congr_fun hπ g
      _ = j q ^ n := by rw [hq, map_pow]
  let t : Lattice →* L := (zpowersHom L u).noncommCoprod (zpowersHom L v)
    (fun a b => (hcomm.zpow_left a.toAdd).zpow_right b.toAdd)
  have ht : π.comp t = j := by
    ext1 a
    change π (u ^ a.1.toAdd * v ^ a.2.toAdd) = j a
    rw [map_mul, map_zpow, map_zpow, image hu hx, image hv hy, ← map_zpow, ← map_zpow,
      ← map_mul, lattice_decomposition]
  obtain ⟨s, hs, _⟩ := hj.2.2 L he.1 he.2.1 t
  obtain ⟨k, _, hk⟩ := hj.2.2 Q hj.1 hj.2.1 j
  refine ⟨L, Q, instL, instQ, e, j, π, s, he, hj, hπ, (hk _ ?_).trans (hk _ ?_).symm⟩
  · change (π.comp s).comp j = j
    rw [MonoidHom.comp_assoc, hs, ht]
  · exact MonoidHom.id_comp j

/--
**Nilpotent extensions that split at every prime need not split.** It is not true that every
extension of nilpotent groups with finitely generated quotient that splits at every prime splits:
there are nilpotent groups $N$, $G$ and $Q$ with $Q$ finitely generated, an injective homomorphism
$i \colon N \to G$ and a surjective homomorphism $\pi \colon G \to Q$ with $\operatorname{im} i =
\ker \pi$, such that the extension splits at every prime $p$ (for some $p$-localizations $G_p$
of $G$ and $Q_p$ of $Q$, the localized quotient map $\pi_p \colon G_p \to Q_p$ has a homomorphic
section) but there is no homomorphism $s \colon Q \to G$ with $\pi \circ s = \mathrm{id}_Q$.

Lorensen constructed such extensions in which $N$, $G$ and $Q$ are finitely generated and
torsion-free.

Source: E. I. Khukhro and V.
D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.93 (P. Hilton); resolution: K.
Lorensen, Nonsplit nilpotent group extensions that split at every prime, Math. Proc. Cambridge
Philos. Soc. 123 (1998), no. 2, 213-215, doi:10.1017/S0305004197002211, introduction (first page,
shown on Cambridge Core): examples of nilpotent group extensions which split at every p-localization
but fail to split, disproving Hilton's conjecture that any nilpotent group extension with finitely
generated quotient which splits at every prime must split; in both families of counterexamples the
groups are torsion-free and finitely generated. Kourovka Archive, Problem 12.93: 'No, not always',
https://doi.org/10.1017/S0305004197002211.
-/
public theorem nilpotentExtensionSplitsIfSplitsAtPrimes_refuted :
    ¬ nilpotentExtensionSplitsIfSplitsAtPrimes := by
  intro h
  have : Group.IsNilpotent Cover := nilpotent_of_central_commutators cover_central
  obtain ⟨s, hs⟩ := h projection.ker Cover Lattice inferInstance inferInstance inferInstance
    inferInstance projection.ker.subtype projection Subtype.val_injective
    (fun q => ⟨⟨q.1.toAdd, q.2.toAdd, 0, 0, 0, 0⟩, rfl⟩) projection.ker.range_subtype
    splits_projection
  exact no_section s hs

end MathlibExt.GroupTheory.NilpotentExtensionSplitAtPrimesKourovka12Problem93Wanted
