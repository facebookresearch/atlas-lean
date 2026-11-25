/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import Mathlib.GroupTheory.Solvable
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Perfectness of the intersection of the derived series (Kourovka Notebook Problem 17.82)

Kourovka Notebook, Archive of Solved Problems, Problem 17.82 (R. Mikhailov): is it true that in
every finitely presented group the intersection of the derived series has trivial abelianization?
A semidirect product with a finite abelian normal subgroup and a free quotient gives a
counterexample.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.82 (R.
Mikhailov). UnsolvedMath record UM-00701384 (`KOU-17.82`), dataset ulamai/UnsolvedMath v1.8.0.

The intersection is `D = ⨅ n, derivedSeries G n` (the `ω`-th term), trivial abelianization is `[D,
D] = D`, and finitely presented is Mathlib's `Group.IsFinitelyPresented`; groups are taken in
`Type`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.DerivedSeriesIntersectionPerfectKourovka17Problem82Wanted

set_option linter.deprecated false in
/-- **Perfectness of the intersection of the derived series (Kourovka 17.82).** The conjecture of
R. Mikhailov that for every finitely presented group $G$, the intersection
$D = \bigcap_{n} G^{(n)}$ of the terms $G^{(n)}$ of the derived series of $G$ satisfies
$[D, D] = D$, that is, $D$ has trivial abelianization. -/
def derivedSeriesIntersectionPerfect : Prop :=
  ∀ (G : Type) [Group G], Group.IsFinitelyPresented G →
    ⁅⨅ n, derivedSeries G n, ⨅ n, derivedSeries G n⁆ = ⨅ n, derivedSeries G n

open Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise Function commutatorElement

private abbrev Free := FreeGroup Bool

private def row (b : Bool) : Fin 2 := if b then 1 else 0
private def col (b : Bool) : Fin 2 := row (!b)

private theorem row_ne_col (b : Bool) : row b ≠ col b := by
  cases b <;> decide

private def shear {R : Type*} [CommRing R] (b : Bool) (c : R) : SL(2, R) :=
  transvection (row_ne_col b) c

private def integerRepresentation : Free →* SL(2, ℤ) :=
  FreeGroup.lift fun b => shear b 2

private def integerShear (b : Bool) : Multiplicative ℤ →* SL(2, ℤ) where
  toFun k := shear b (k.toAdd * 2)
  map_one' := by simp [shear]
  map_mul' x y := by
    change shear b ((x.toAdd + y.toAdd) * 2) = _
    rw [add_mul]
    exact transvection_add _ _ _

private theorem abs_lt_abs_add_shear {x y k : ℤ} (h : |x| < |y|) (hk : k ≠ 0) :
    |y| < |x + k * 2 * y| := by
  have hk' : 1 ≤ |k| := by
    have := abs_pos.mpr hk
    omega
  have hbound : 2 * |y| ≤ |k * 2 * y| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by decide : (0 : ℤ) ≤ 2)]
    calc
      2 * |y| = 1 * 2 * |y| := by simp
      _ ≤ |k| * 2 * |y| := by gcongr
  -- Subtracting x from the new coordinate gives a term of size at least 2|y|.
  have htri' := abs_sub (x + k * 2 * y) x
  rw [add_sub_cancel_left] at htri'
  omega

private def pingPongSet (b : Bool) : Set (Fin 2 → ℤ) :=
  {v | |v (col b)| < |v (row b)|}

private theorem shear_smul_row {R : Type*} [CommRing R] (b : Bool) (c : R)
    (v : Fin 2 → R) : (shear b c • v) (row b) = v (row b) + c * v (col b) := by
  simp [shear, SpecialLinearGroup.smul_def, transvection_coe, add_mulVec, single_mulVec_eq]

private theorem shear_smul_col {R : Type*} [CommRing R] (b : Bool) (c : R)
    (v : Fin 2 → R) : (shear b c • v) (col b) = v (col b) := by
  simp [shear, SpecialLinearGroup.smul_def, transvection_coe, add_mulVec, single_mulVec_eq,
    (row_ne_col b).symm]

private theorem integerRepresentation_injective : Function.Injective integerRepresentation := by
  classical
  let e : FreeGroup Unit ≃* Multiplicative ℤ := FreeGroup.mulEquivIntOfUnique
  let f : Bool → FreeGroup Unit →* SL(2, ℤ) := fun b =>
    (integerShear b).comp e.toMonoidHom
  have hf : integerRepresentation =
      (Monoid.CoprodI.lift f).comp (@freeGroupEquivCoprodI Bool).toMonoidHom := by
    apply FreeGroup.ext_hom
    intro b
    simp [integerRepresentation, f, freeGroupEquivCoprodI, integerShear, e,
      FreeGroup.mulEquivIntOfUnique, FreeGroup.equivIntOfUnique]
  rw [hf]
  refine (Monoid.CoprodI.lift_injective_of_ping_pong f ?_ pingPongSet ?_ ?_ ?_).comp
    freeGroupEquivCoprodI.injective
  · right
    have h3 : (3 : Cardinal) < Cardinal.aleph0 := by
      exact_mod_cast (Cardinal.natCast_lt_aleph0 (n := 3))
    exact ⟨false, h3.le.trans ((Cardinal.aleph0_le_mk ℤ).trans (Cardinal.mk_congr
      (Multiplicative.ofAdd.trans e.toEquiv.symm)).le)⟩
  · intro b
    refine ⟨Pi.single (row b) 1, ?_⟩
    simp [pingPongSet, (row_ne_col b).symm]
  · intro b c hbc
    have hc : c = !b := by cases b <;> cases c <;> simp_all
    subst c
    refine Set.disjoint_left.mpr fun v hv hw => ?_
    simp only [pingPongSet, Set.mem_ofPred_eq, col, Bool.not_not] at hv hw
    exact (lt_asymm hv) hw
  · intro b c hbc g hg
    have hc : c = !b := by cases b <;> cases c <;> simp_all
    subst c
    rintro _ ⟨v, hv, rfl⟩
    have hv' : |v (row b)| < |v (col b)| := by simpa [pingPongSet, col] using hv
    have hg' : (e g).toAdd ≠ 0 :=
      fun he => hg (e.injective (by simpa using he))
    change (shear b ((e g).toAdd * 2) • v) ∈ pingPongSet b
    unfold pingPongSet
    simp only [Set.mem_ofPred_eq, shear_smul_col, shear_smul_row]
    exact abs_lt_abs_add_shear hv' hg'

private def reduce (m : ℕ) : SL(2, ℤ) →* SL(2, ZMod m) :=
  SpecialLinearGroup.map (Int.castRingHom (ZMod m))

private theorem reduce_shear (m : ℕ) (b : Bool) (k : ℤ) :
    reduce m (shear b k) = shear b (k : ZMod m) := by
  apply Subtype.ext
  change ((Int.castRingHom (ZMod m)).mapMatrix (shear b k).val) = (shear b (k : ZMod m)).val
  rw [shear, shear, transvection_coe, transvection_coe, map_add, map_one]
  exact congrArg (1 + ·) (Matrix.map_single _ _ _ (Int.castRingHom (ZMod m)))

private theorem reduce_eq_iff (m : ℕ) (a b : SL(2, ℤ)) :
    reduce m a = reduce m b ↔ ∀ i j, (m : ℤ) ∣ b.1 i j - a.1 i j := by
  constructor
  · intro h i j
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ m).mp
      (congrArg (fun g : SL(2, ZMod m) => g.val i j) h)
  · intro h
    apply Subtype.ext
    exact Matrix.ext fun i j => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ m).mpr (h i j)

-- Commutators of matrices congruent to 1 modulo 2^k are congruent to 1 modulo 2^(k+1).
private theorem reduce_commutator (k : ℕ) (hk : 1 ≤ k) (a b : SL(2, ℤ))
    (ha : reduce (2 ^ k) a = 1) (hb : reduce (2 ^ k) b = 1) :
    reduce (2 ^ (k + 1)) ⁅a, b⁆ = 1 := by
  have displacement {g : SL(2, ℤ)} (hg : reduce (2 ^ k) g = 1) :
      ∃ A : Matrix (Fin 2) (Fin 2) ℤ, g.val = 1 + (2 : ℤ) ^ k • A := by
    have h := (reduce_eq_iff (2 ^ k) 1 g).mp (by simpa using hg.symm)
    simp only [Nat.cast_pow, Nat.cast_ofNat] at h
    choose A hA using h
    refine ⟨Matrix.of A, Matrix.ext fun i j => ?_⟩
    have hij := hA i j
    change g.val i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j = _ at hij
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    omega
  obtain ⟨A, hA⟩ := displacement ha
  obtain ⟨B, hB⟩ := displacement hb
  have hdiff : (a * b).val - (b * a).val =
      (2 : ℤ) ^ (k + k) • (A * B - B * A) := by
    change a.val * b.val - b.val * a.val = _
    rw [hA, hB]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
      smul_add, smul_smul, ← pow_add, smul_sub]
    abel
  have hcomm : reduce (2 ^ (k + 1)) (b * a) = reduce (2 ^ (k + 1)) (a * b) := by
    apply (reduce_eq_iff _ _ _).mpr
    intro i j
    rw [Nat.cast_pow, Nat.cast_ofNat]
    refine (pow_dvd_pow (2 : ℤ) (by omega : k + 1 ≤ k + k)).trans ?_
    exact ⟨(A * B - B * A) i j, congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M i j) hdiff⟩
  simpa only [map_mul, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    using hcomm.symm

private theorem derivedSeries_congruent (n : ℕ) :
    Subgroup.derivedSeries Free n ≤ ((reduce (2 ^ (n + 1))).comp integerRepresentation).ker := by
  induction n with
  | zero =>
    rw [Subgroup.derivedSeries_zero, ← FreeGroup.closure_range_of, closure_le]
    rintro _ ⟨b, rfl⟩
    change reduce 2 (FreeGroup.lift (fun b => shear b (2 : ℤ)) (FreeGroup.of b)) = 1
    rw [FreeGroup.lift_apply_of, reduce_shear]
    change shear b (2 : ZMod 2) = 1
    rw [show (2 : ZMod 2) = 0 by decide]
    exact transvection_coeff_zero _
  | succ n ih =>
    rw [Subgroup.derivedSeries_succ]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    exact ((reduce (2 ^ (n + 2))).comp integerRepresentation).mem_ker.mpr
      (by simpa only [MonoidHom.comp_apply, map_commutatorElement] using
        reduce_commutator (n + 1) (by omega) _ _ (ih ha) (ih hb))

private theorem free_intersection_eq_bot : (⨅ n, Subgroup.derivedSeries Free n) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => integerRepresentation_injective ?_
  rw [map_one]
  apply Subtype.ext
  ext i j
  have h (n : ℕ) : (2 : ℤ) ^ (n + 1) ∣
      (integerRepresentation g).val i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    have hn := (derivedSeries_congruent n) (Subgroup.mem_iInf.mp hg n)
    have hd := (reduce_eq_iff _ 1 (integerRepresentation g)).mp (by simpa using hn.symm) i j
    rw [Nat.cast_pow, Nat.cast_ofNat, SpecialLinearGroup.coe_one] at hd
    exact hd
  apply sub_eq_zero.mp
  let x := (integerRepresentation g).val i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j
  change x = 0
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (h x.natAbs) ?_
  rw [Int.natAbs_pow]
  change x.natAbs < 2 ^ (x.natAbs + 1)
  exact (Nat.lt_succ_self _).trans Nat.lt_two_pow_self

private theorem modFivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

attribute [local instance] modFivePrime

private def finiteRepresentation : Free →* SL(2, ZMod 5) :=
  (reduce 5).comp integerRepresentation

private theorem shear_range (b : Bool) (c : ZMod 5) : shear b c ∈ finiteRepresentation.range := by
  let S : Multiplicative (ZMod 5) →* SL(2, ZMod 5) :=
    { toFun := fun x => shear b x.toAdd
      map_one' := by simp [shear]
      map_mul' := fun x y => transvection_add (row_ne_col b) x.toAdd y.toAdd }
  let q : ZMod 5 := c / (2 : ZMod 5)
  refine ⟨FreeGroup.of b ^ q.val, ?_⟩
  rw [map_pow]
  have hgen : finiteRepresentation (FreeGroup.of b) = shear b (2 : ZMod 5) := by
    simp [finiteRepresentation, integerRepresentation, reduce_shear]
  rw [hgen]
  change (S (Multiplicative.ofAdd 2)) ^ q.val = S (Multiplicative.ofAdd c)
  rw [← map_pow]
  congr 1
  change q.val • (2 : ZMod 5) = c
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
  exact div_mul_cancel₀ c (by decide : (2 : ZMod 5) ≠ 0)

private theorem finiteRepresentation_surjective : Function.Surjective finiteRepresentation := by
  intro a
  change a ∈ finiteRepresentation.range
  apply Matrix.SL2.transvection_induction (F := ZMod 5) (· ∈ finiteRepresentation.range) _ _ a
  · intro i j h c
    have hi : i = 0 ∨ i = 1 := by omega
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (h rfl).elim
    · exact shear_range false c
    · exact shear_range true c
    · exact (h rfl).elim
  · intro a b
    exact finiteRepresentation.range.mul_mem

private theorem finite_derivedSeries (n : ℕ) : Subgroup.derivedSeries SL(2, ZMod 5) n = ⊤ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Subgroup.derivedSeries_succ, ih, ← commutator_def]
    have h₂ : (2 : ZMod 5) ≠ 0 := by decide
    have h₄ : (2 : ZMod 5) ^ 2 ≠ 1 := by decide
    exact Matrix.SL2.commutator_eq_top (F := ZMod 5) h₂ h₄

-- Include the multiplication table of the finite factor and the action of each free generator.
private def semidirectRelations {A : Type*} [Group A] (φ : Free →* MulAut A) :
    Set (FreeGroup (A ⊕ Bool)) :=
  Set.range (fun (p : A × A) =>
    FreeGroup.of (Sum.inl p.1) * FreeGroup.of (Sum.inl p.2) *
      (FreeGroup.of (Sum.inl (p.1 * p.2)))⁻¹) ∪
  Set.range (fun (p : Bool × A) =>
    FreeGroup.of (Sum.inr p.1) * FreeGroup.of (Sum.inl p.2) *
      (FreeGroup.of (Sum.inr p.1))⁻¹ * (FreeGroup.of (Sum.inl (φ (FreeGroup.of p.1) p.2)))⁻¹)

private theorem semidirect_finitelyPresented {A : Type*} [Group A] [Finite A]
    (φ : Free →* MulAut A) : Group.IsFinitelyPresented (A ⋊[φ] Free) := by
  let R := semidirectRelations φ
  let P := PresentedGroup R
  let a : A → P := fun x => PresentedGroup.of (Sum.inl x)
  let s : Bool → P := fun b => PresentedGroup.of (Sum.inr b)
  have ha (x y : A) : a x * a y = a (x * y) := by
    exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (show _ ∈ R from Or.inl ⟨(x, y), rfl⟩)
  let fa : A →* P := MonoidHom.mk' a (fun x y => (ha x y).symm)
  let fs : Free →* P := FreeGroup.lift s
  have hconj (g : Free) :
      ∀ x, fa (φ g x) = MulAut.conj (fs g) (fa x) := by
    induction g using FreeGroup.induction_on with
    | one => simp
    | of b =>
      intro x
      rw [MulAut.conj_apply]
      exact (PresentedGroup.mk_eq_mk_of_mul_inv_mem
        (show _ ∈ R from Or.inr ⟨(b, x), rfl⟩)).symm
    | inv_of b ih =>
      intro x
      simp only [map_inv]
      let C := MulAut.conj (fs (FreeGroup.of b))
      change fa ((φ (FreeGroup.of b))⁻¹ x) = C⁻¹ (fa x)
      apply C.injective
      rw [MulAut.apply_inv_self, ← ih, MulAut.apply_inv_self]
    | mul g h ihg ihh =>
      intro x
      simp only [map_mul, MulAut.mul_apply, ihg, ihh]
  let forward : A ⋊[φ] Free →* P :=
    SemidirectProduct.lift fa fs (fun g => MonoidHom.ext (hconj g))
  let gen : A ⊕ Bool → A ⋊[φ] Free :=
    Sum.elim SemidirectProduct.inl (SemidirectProduct.inr ∘ FreeGroup.of)
  have hrel : ∀ w ∈ R, FreeGroup.lift gen w = 1 := by
    rintro _ (⟨⟨x, y⟩, rfl⟩ | ⟨⟨b, x⟩, rfl⟩)
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, gen, Sum.elim_inl]
      rw [← map_mul, mul_inv_cancel]
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, gen, Sum.elim_inl,
        Sum.elim_inr, Function.comp_apply]
      rw [← map_inv, ← SemidirectProduct.inl_aut, mul_inv_cancel]
  let backward : P →* A ⋊[φ] Free := PresentedGroup.toGroup hrel
  have hleft (x : A) : backward (fa x) = SemidirectProduct.inl x :=
    PresentedGroup.toGroup.of hrel
  have hright (b : Bool) : backward (s b) = SemidirectProduct.inr (FreeGroup.of b) :=
    PresentedGroup.toGroup.of hrel
  have h₁ : forward.comp backward = MonoidHom.id P := by
    apply PresentedGroup.ext
    intro x
    cases x with
    | inl x =>
      change forward (backward (fa x)) = fa x
      rw [hleft, SemidirectProduct.lift_inl]
    | inr b =>
      change forward (backward (s b)) = s b
      rw [hright, SemidirectProduct.lift_inr, FreeGroup.lift_apply_of]
  have h₂ : backward.comp forward = MonoidHom.id (A ⋊[φ] Free) := by
    apply SemidirectProduct.hom_ext
    · apply MonoidHom.ext
      intro x
      change backward (forward (SemidirectProduct.inl x)) = SemidirectProduct.inl x
      rw [show forward (SemidirectProduct.inl x) = fa x from SemidirectProduct.lift_inl _ _ _ _]
      exact hleft x
    · apply FreeGroup.ext_hom
      intro b
      change backward (forward (SemidirectProduct.inr (FreeGroup.of b))) = _
      rw [show forward (SemidirectProduct.inr (FreeGroup.of b)) = fs (FreeGroup.of b) from
        SemidirectProduct.lift_inr _ _ _ _, FreeGroup.lift_apply_of]
      exact hright b
  have : Finite R := Set.Finite.to_subtype ((Set.finite_range _).union (Set.finite_range _))
  exact Group.IsFinitelyPresented.equiv (MonoidHom.toMulEquiv backward forward h₁ h₂)

private abbrev V := Fin 2 → ZMod 5

private def action : Free →* MulAut (Multiplicative V) where
  toFun g := (DistribMulAction.toAddEquiv V (finiteRepresentation g)).toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro v
    apply Multiplicative.toAdd.injective
    change finiteRepresentation 1 • v.toAdd = v.toAdd
    rw [map_one, one_smul]
  map_mul' g h := by
    apply MulEquiv.ext
    intro v
    apply Multiplicative.toAdd.injective
    change finiteRepresentation (g * h) • v.toAdd =
      finiteRepresentation g • finiteRepresentation h • v.toAdd
    rw [map_mul, mul_smul]

private abbrev Counterexample := Multiplicative V ⋊[action] Free

private abbrev translation : Multiplicative V →* Counterexample := SemidirectProduct.inl

private theorem intersection_le_translations :
    (⨅ n, Subgroup.derivedSeries Counterexample n) ≤ translation.range := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  intro g hg
  apply MonoidHom.mem_ker.mpr
  have hmem : g.right ∈ ⨅ n, Subgroup.derivedSeries Free n := by
    refine Subgroup.mem_iInf.mpr fun n => ?_
    exact Subgroup.map_derivedSeries_le_derivedSeries SemidirectProduct.rightHom n
      ⟨g, Subgroup.mem_iInf.mp hg n, rfl⟩
  simpa [free_intersection_eq_bot] using hmem

private theorem translations_le_derivedSeries (n : ℕ) :
    translation.range ≤ Subgroup.derivedSeries Counterexample n := by
  induction n with
  | zero => exact le_top
  | succ n ih =>
    rintro _ ⟨v, rfl⟩
    have hn : (-(1 : ZMod 5)) ≠ 0 := by decide
    let m := diag2 (-(1 : ZMod 5)) hn
    have hm (w : V) : m • w = -w := by
      funext i
      fin_cases i <;>
        simp [m, SpecialLinearGroup.smul_def, diag2_coe, Matrix.mulVec_diagonal]
    have himage : (Subgroup.derivedSeries Free n).map finiteRepresentation = ⊤ := by
      rw [Subgroup.map_derivedSeries_eq finiteRepresentation_surjective n, finite_derivedSeries]
    have hm' : m ∈ (Subgroup.derivedSeries Free n).map finiteRepresentation := by
      rw [himage]
      exact Subgroup.mem_top m
    obtain ⟨g, hg, hgm⟩ := Subgroup.mem_map.mp hm'
    have hg' : (SemidirectProduct.inr g : Counterexample) ∈
        Subgroup.derivedSeries Counterexample n :=
      Subgroup.map_derivedSeries_le_derivedSeries SemidirectProduct.inr n ⟨g, hg, rfl⟩
    let w : Multiplicative V := Multiplicative.ofAdd (fun i => 2 * v.toAdd i)
    have hw : action g w * w⁻¹ = v := by
      change Multiplicative.ofAdd (finiteRepresentation g • w.toAdd + -w.toAdd) = v
      rw [← sub_eq_add_neg]
      rw [hgm, hm]
      apply Multiplicative.toAdd.injective
      funext i
      change -(2 * v.toAdd i) - 2 * v.toAdd i = v.toAdd i
      calc
        _ = (-4 : ZMod 5) * v.toAdd i := by ring
        _ = _ := by rw [show (-4 : ZMod 5) = 1 by decide, one_mul]
    have hcomm : ⁅(SemidirectProduct.inr g : Counterexample), translation w⁆ = translation v := by
      rw [commutatorElement_def, ← map_inv (SemidirectProduct.inr (φ := action)),
        ← SemidirectProduct.inl_aut, ← map_inv translation, ← map_mul, hw]
    rw [← hcomm, Subgroup.derivedSeries_succ]
    exact Subgroup.commutator_mem_commutator hg' (ih ⟨w, rfl⟩)

private theorem intersection_eq_translations :
    (⨅ n, Subgroup.derivedSeries Counterexample n) = translation.range :=
  le_antisymm intersection_le_translations (le_iInf translations_le_derivedSeries)

/--
**The intersection of the derived series need not be perfect.** There exists a finitely presented
group $G$ such that the intersection $D = \bigcap_{n} G^{(n)}$ of the terms $G^{(n)}$ of the
derived series of $G$ satisfies $[D, D] \ne D$. That is, the conjecture of Kourovka Problem 17.82
is false; the Kourovka Archive credits this answer to V. A. Roman'kov (2011).

Source: E.
I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.82 (R. Mikhailov);
resolution: V. A. Roman'kov, Siberian Math. J. 52 (2011), 348-351, Kourovka Archive, Problem 17.82
(No, not always).
-/
theorem derivedSeriesIntersectionPerfect_refuted : ¬ derivedSeriesIntersectionPerfect := by
  intro h
  have hperfect := h Counterexample (semidirect_finitelyPresented action)
  change ⁅⨅ n, Subgroup.derivedSeries Counterexample n,
    ⨅ n, Subgroup.derivedSeries Counterexample n⁆ = ⨅ n, Subgroup.derivedSeries Counterexample n
    at hperfect
  rw [intersection_eq_translations] at hperfect
  have hab : ⁅translation.range, translation.range⁆ = ⊥ := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
      (commutator_eq_bot_iff _).mpr inferInstance, Subgroup.map_bot]
  have ht : translation (Multiplicative.ofAdd (fun _ => (1 : ZMod 5))) ∈ translation.range :=
    ⟨_, rfl⟩
  rw [← hperfect, hab, Subgroup.mem_bot] at ht
  have hz := SemidirectProduct.inl_injective (ht.trans (map_one translation).symm)
  exact (by decide : (1 : ZMod 5) ≠ 0) (congrArg (fun v : Multiplicative V => v.toAdd 0) hz)

end MathlibExt.GroupTheory.DerivedSeriesIntersectionPerfectKourovka17Problem82Wanted
