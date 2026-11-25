/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.LinearAlgebra.ExteriorAlgebra.PrimitiveFree
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# A higher exterior primitive on an actual nonfree module in characteristic two

Let `k = ZMod 2`, `R = k ⊕ k³` be the native trivial square-zero extension,
and `x`, `y`, `z` its three square-zero generators. In the quotient of `R³`
by `x e₁ + y e₂`, `x e₀ + z e₂`, and `y e₀ + z e₁`, the degree-two word

`x (m₀ ∧ m₁) + y (m₀ ∧ m₂) + z (m₁ ∧ m₂)`

has zero actual reduced coproduct. Its nonvanishing is detected by an actual
`R`-alternating map to a second explicitly presented quotient, followed by
an actual `k`-linear detector. The detector is deliberately kept over `k`:
the sum of these nilpotent coefficient coordinates is not `R`-linear to
`k` with its augmentation action.

No primitive condition, nonzero condition, rank certificate, or coalgebra
certificate is assumed. The example shows why the free-module hypothesis
in `ExteriorAlgebra.primitive_homogeneous_eq_zero` must be retained.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace ChevalleyEilenbergCharacteristicTwoPrimitive

abbrev k := ZMod 2
abbrev V := Fin 3 → k
abbrev R := TrivSqZeroExt k V
abbrev F := Fin 3 → R

local instance : Algebra k R := inferInstanceAs (Algebra (ZMod 2) (TrivSqZeroExt k V))
local instance : IsScalarTower k R F where
  smul_assoc c r a := by
    funext i
    change (c • r) * a i = c • (r * a i)
    exact Algebra.smul_mul_assoc c r (a i)

/-- The native coefficient ring has characteristic two. -/
theorem two_eq_zero : (2 : R) = 0 := by
  apply TrivSqZeroExt.ext
  · change (2 : k) = 0
    decide
  · ext i
    change (0 : k) = 0
    rfl

private theorem add_self_eq_zero {A : Type*} [AddCommGroup A] [Module R A] (a : A) :
    a + a = 0 := by
  exact (two_smul R a).symm.trans
    ((congrArg (fun r : R => r • a) two_eq_zero).trans (zero_smul R a))

private theorem neg_eq_self {A : Type*} [AddCommGroup A] [Module R A] (a : A) :
    -a = a := (eq_neg_of_add_eq_zero_left (add_self_eq_zero a)).symm

/-- The three actual square-zero coefficients in the native extension. -/
def nil (i : Fin 3) : R := TrivSqZeroExt.inr (Pi.single i 1)

/-- The actual standard coordinate vectors of `R³`. -/
def e (i : Fin 3) : F := Pi.single i 1

/-- The three presentation relations. -/
def relation : Fin 3 → F :=
  ![nil 0 • e 1 + nil 1 • e 2,
    nil 0 • e 0 + nil 2 • e 2,
    nil 1 • e 0 + nil 2 • e 1]

def relations : Submodule R F := Submodule.span R (Set.range relation)

/-- The concrete nonfree module on which the higher primitive lives. -/
abbrev M := F ⧸ relations

def m (i : Fin 3) : M := relations.mkQ (e i)

private theorem relation_eq_zero (i : Fin 3) : relations.mkQ (relation i) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero relations).mpr
  exact Submodule.subset_span ⟨i, rfl⟩

theorem relation_zero : nil 0 • m 1 + nil 1 • m 2 = 0 := by
  simpa only [relation, Matrix.cons_val_zero, m, map_add, map_smul] using relation_eq_zero 0

theorem relation_one : nil 0 • m 0 + nil 2 • m 2 = 0 := by
  simpa only [relation, Matrix.cons_val_succ, Matrix.cons_val_zero, m,
    map_add, map_smul, Matrix.cons_val_one] using relation_eq_zero 1

theorem relation_two : nil 1 • m 0 + nil 2 • m 1 = 0 := by
  have h : relations.mkQ (nil 1 • e 0 + nil 2 • e 1) = 0 := relation_eq_zero 2
  simpa only [m, map_add, map_smul] using h

/-- The ordinary characteristic-two alternating coordinate cross product on `R³`. -/
def cross : F →ₗ[R] F →ₗ[R] F where
  toFun a :=
    { toFun b := ![a 0 * b 1 + a 1 * b 0,
        a 0 * b 2 + a 2 * b 0, a 1 * b 2 + a 2 * b 1]
      map_add' b c := by
        apply funext
        intro i
        fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, mul_add, add_mul] <;> ring
      map_smul' r b := by
        apply funext
        intro i
        fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, smul_eq_mul] <;> ring }
  map_add' a b := by
    apply LinearMap.ext
    intro c
    apply funext
    intro i
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, mul_add, add_mul] <;> ring
  map_smul' r a := by
    apply LinearMap.ext
    intro b
    apply funext
    intro i
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, smul_eq_mul] <;> ring

@[simp]
theorem cross_apply (a b : F) :
    cross a b = ![a 0 * b 1 + a 1 * b 0,
      a 0 * b 2 + a 2 * b 0, a 1 * b 2 + a 2 * b 1] := rfl

theorem cross_symm (a b : F) : cross a b = cross b a := by
  apply funext
  intro i
  fin_cases i <;> simp only [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_succ] <;> ring

private theorem cross_self (a : F) : cross a a = 0 := by
  apply funext
  intro i
  fin_cases i <;>
    simp only [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_succ, Pi.zero_apply]
  · rw [mul_comm (a 1) (a 0)]
    exact add_self_eq_zero _
  · rw [mul_comm (a 2) (a 0)]
    exact add_self_eq_zero _
  · rw [mul_comm (a 2) (a 1)]
    exact add_self_eq_zero _

/-- The actual relations in the target of the alternating detector. -/
def targetRelations : Submodule R F :=
  Submodule.span R (Set.range (fun ij : Fin 3 × Fin 3 => cross (relation ij.1) (e ij.2)))

abbrev N := F ⧸ targetRelations

theorem cross_relation_mem (i : Fin 3) (a : F) : cross (relation i) a ∈ targetRelations := by
  rw [← (Pi.basisFun R (Fin 3)).sum_repr a, map_sum]
  apply Submodule.sum_mem
  intro j _
  rw [map_smul]
  apply Submodule.smul_mem
  have he : (Pi.basisFun R (Fin 3)) j = e j := by
    apply funext
    intro l
    simp only [Pi.basisFun_apply, e]
  have hm : cross (relation i) (e j) ∈ targetRelations :=
    Submodule.subset_span ⟨(i, j), rfl⟩
  exact (congrArg (fun x => cross (relation i) x ∈ targetRelations) he).mpr hm


theorem cross_mem_of_mem_relations (a : F) (ha : a ∈ relations) :
    ∀ b : F, cross a b ∈ targetRelations := by
  refine Submodule.span_induction (p := fun a _ => ∀ b : F, cross a b ∈ targetRelations)
    ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨i, rfl⟩ b
    exact cross_relation_mem i b
  · intro b
    simpa only [map_zero, LinearMap.zero_apply] using targetRelations.zero_mem
  · intro a b _ _ ha hb c
    simpa only [map_add, LinearMap.add_apply] using targetRelations.add_mem (ha c) (hb c)
  · intro r a _ ha b
    simpa only [map_smul, LinearMap.smul_apply] using targetRelations.smul_mem r (ha b)

private def crossQuotient : F →ₗ[R] F →ₗ[R] N where
  toFun a := targetRelations.mkQ.comp (cross a)
  map_add' a b := by
    apply LinearMap.ext
    intro c
    simp only [LinearMap.comp_apply, map_add, LinearMap.add_apply]
  map_smul' r a := by
    apply LinearMap.ext
    intro c
    simp only [LinearMap.comp_apply, map_smul, LinearMap.smul_apply, RingHom.id_apply]

private theorem relations_le_ker_crossQuotient : relations ≤ crossQuotient.ker := by
  intro a ha
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro b
  apply (Submodule.Quotient.mk_eq_zero targetRelations).mpr
  exact cross_mem_of_mem_relations a ha b

private theorem relations_le_ker_crossQuotient_flip : relations ≤ crossQuotient.flip.ker := by
  intro a ha
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro b
  change targetRelations.mkQ (cross b a) = 0
  rw [cross_symm b a]
  apply (Submodule.Quotient.mk_eq_zero targetRelations).mpr
  exact cross_mem_of_mem_relations a ha b

/-- The actual bilinear descent through both presentation quotients. -/
def bilinear : M →ₗ[R] M →ₗ[R] N := by
  let f : F →ₗ[R] F →ₗ[R] N :=
    { toFun a := targetRelations.mkQ.comp (cross a)
      map_add' a b := by apply LinearMap.ext; intro c; simp only [LinearMap.comp_apply, map_add, LinearMap.add_apply]
      map_smul' r a := by apply LinearMap.ext; intro c; simp only [LinearMap.comp_apply, map_smul,
    LinearMap.smul_apply, RingHom.id_apply] }
  have h₁ : relations ≤ f.ker := by
    intro a ha
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro b
    exact (Submodule.Quotient.mk_eq_zero targetRelations).mpr
      (cross_mem_of_mem_relations a ha b)
  have h₂ : relations ≤ f.flip.ker := by
    intro a ha
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro b
    change targetRelations.mkQ (cross b a) = 0
    rw [cross_symm]
    exact (Submodule.Quotient.mk_eq_zero targetRelations).mpr
      (cross_mem_of_mem_relations a ha b)
  exact f.liftQ₂ relations relations h₁ h₂

@[simp]
theorem bilinear_mk (a b : F) :
    bilinear (relations.mkQ a) (relations.mkQ b) = targetRelations.mkQ (cross a b) := rfl

private theorem bilinear_self (a : M) : bilinear a a = 0 := by
  refine Submodule.Quotient.induction_on relations a ?_
  intro a
  change bilinear (relations.mkQ a) (relations.mkQ a) = 0
  rw [bilinear_mk, cross_self, map_zero]

/-- The descended form is genuinely alternating, including its diagonal-zero law. -/
def alternating : M [⋀^Fin 2]→ₗ[R] N where
  toFun v := bilinear (v 0) (v 1)
  map_update_add' := by
    intro _ v i a b
    fin_cases i <;> simp [map_add]
  map_update_smul' := by
    intro _ v i r a
    fin_cases i <;> simp [map_smul]
  map_eq_zero_of_eq' := by
    intro v i j h hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change v 0 = v 1 at h
      exact (congrArg (fun x => bilinear x (v 1)) h).trans (bilinear_self (v 1))
    · change v 1 = v 0 at h
      exact (congrArg (fun x => bilinear (v 0) x) h).trans (bilinear_self (v 0))
    · exact (hij rfl).elim

/-- The actual exterior universal property, with the earned alternating form. -/
def exteriorDetector : (⋀[R]^2 M) →ₗ[R] N :=
  exteriorPower.alternatingMapLinearEquiv alternating

def wedge (i j : Fin 3) : ⋀[R]^2 M := exteriorPower.ιMulti R 2 ![m i, m j]

@[simp]
theorem wedge_coe (i j : Fin 3) :
    (wedge i j : ExteriorAlgebra R M) = ExteriorAlgebra.ι R (m i) * ExteriorAlgebra.ι R (m j) := by
  simp [wedge, ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply]

@[simp]
theorem exteriorDetector_wedge (i j : Fin 3) :
    exteriorDetector (wedge i j) = targetRelations.mkQ (cross (e i) (e j)) := by
  rw [exteriorDetector, wedge, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change bilinear (m i) (m j) = _
  exact bilinear_mk (e i) (e j)

private theorem cross_e_zero_one : cross (e 0) (e 1) = e 0 := by
  apply funext
  intro i
  fin_cases i <;> simp [cross_apply, e, Pi.single_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

private theorem cross_e_zero_two : cross (e 0) (e 2) = e 1 := by
  apply funext
  intro i
  fin_cases i <;> simp [cross_apply, e, Pi.single_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

private theorem cross_e_one_two : cross (e 1) (e 2) = e 2 := by
  apply funext
  intro i
  fin_cases i <;> simp [cross_apply, e, Pi.single_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- The detector on nilpotent coefficients is over `k`, not over `R`. -/
def nilCoordinate : F →ₗ[k] k where
  toFun a := (a 0).snd 0 + (a 1).snd 1 + (a 2).snd 2
  map_add' a b := by simp [TrivSqZeroExt.snd_add] <;> ring
  map_smul' c a := by simp [TrivSqZeroExt.snd_smul, smul_eq_mul] <;> ring

@[simp]
theorem nilCoordinate_apply (a : F) :
    nilCoordinate a = (a 0).snd 0 + (a 1).snd 1 + (a 2).snd 2 := rfl

private theorem relation_fst (i j : Fin 3) : (relation i j).fst = 0 := by
  fin_cases i <;> fin_cases j <;> simp [relation, nil, e, Pi.single_apply, smul_eq_mul]

private theorem cross_relation_fst (i j l : Fin 3) :
    (cross (relation i) (e j) l).fst = 0 := by
  fin_cases l <;> simp [relation_fst]

private theorem nilCoordinate_cross_relation (i j : Fin 3) :
    nilCoordinate (cross (relation i) (e j)) = 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [relation, nil, e, Pi.single_apply, smul_eq_mul,
      TrivSqZeroExt.snd_mul, op_smul_eq_smul] <;> decide

private theorem nilCoordinate_smul_of_fst_zero (r : R) (a : F)
    (ha : ∀ i, (a i).fst = 0) : nilCoordinate (r • a) = r.fst * nilCoordinate a := by
  have h (i j : Fin 3) : ((r • a i).snd j) = r.fst * (a i).snd j := by
    change ((r * a i).snd j) = _
    rw [TrivSqZeroExt.snd_mul, ha i]
    simp [op_smul_eq_smul, smul_eq_mul]
  simp only [nilCoordinate_apply, Pi.smul_apply, h]
  ring

theorem targetRelations_invariants (a : F) (ha : a ∈ targetRelations) :
    (∀ i, (a i).fst = 0) ∧ nilCoordinate a = 0 := by
  refine Submodule.span_induction
    (p := fun a _ => (∀ i, (a i).fst = 0) ∧ nilCoordinate a = 0) ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨⟨i, j⟩, rfl⟩
    exact ⟨cross_relation_fst i j, nilCoordinate_cross_relation i j⟩
  · constructor
    · intro i
      simp
    · exact map_zero nilCoordinate
  · intro a b _ _ ha hb
    constructor
    · intro i
      simp only [Pi.add_apply, TrivSqZeroExt.fst_add, ha.1 i, hb.1 i, zero_add]
    · rw [map_add, ha.2, hb.2, zero_add]
  · intro r a _ ha
    constructor
    · intro i
      change (r * a i).fst = 0
      rw [TrivSqZeroExt.fst_mul, ha.1 i, mul_zero]
    · rw [nilCoordinate_smul_of_fst_zero r a ha.1, ha.2, mul_zero]

private theorem targetRelations_le_ker_nilCoordinate :
    targetRelations.restrictScalars k ≤ nilCoordinate.ker := by
  intro a ha
  exact (targetRelations_invariants a ha).2

/-- The actual quotient detector, with the native comparison of scalar-restricted quotients. -/
def detector : N →ₗ[k] k :=
  ((targetRelations.restrictScalars k).liftQ nilCoordinate
    (by
      intro a ha
      exact (targetRelations_invariants a ha).2)).comp
      (Submodule.Quotient.restrictScalarsEquiv k targetRelations).symm.toLinearMap

@[simp]
theorem detector_mk (a : F) : detector (targetRelations.mkQ a) = nilCoordinate a := by
  rw [detector, LinearMap.comp_apply]
  change (targetRelations.restrictScalars k).liftQ nilCoordinate
    targetRelations_le_ker_nilCoordinate
      ((Submodule.Quotient.restrictScalarsEquiv k targetRelations).symm
        (Submodule.Quotient.mk a)) = _
  rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.liftQ_apply]

/-- The concrete homogeneous degree-two element. -/
def higherPrimitive : ⋀[R]^2 M := nil 0 • wedge 0 1 + nil 1 • wedge 0 2 + nil 2 • wedge 1 2

private theorem exteriorDetector_higherPrimitive :
    exteriorDetector higherPrimitive = targetRelations.mkQ ![nil 0, nil 1, nil 2] := by
  have he : nil 0 • e 0 + nil 1 • e 1 + nil 2 • e 2 = ![nil 0, nil 1, nil 2] := by
    apply funext
    intro i
    fin_cases i <;> simp [e, Pi.single_apply, smul_eq_mul]
  simp only [higherPrimitive, map_add, map_smul, exteriorDetector_wedge,
    cross_e_zero_one, cross_e_zero_two, cross_e_one_two]
  rw [← map_smul, ← map_smul, ← map_smul, ← map_add, ← map_add, he]

/-- The actual detector takes the higher element to `1`, so its nonvanishing is earned. -/
theorem detector_higherPrimitive : detector (exteriorDetector higherPrimitive) = 1 := by
  rw [exteriorDetector_higherPrimitive, detector_mk]
  norm_num [nil] <;> decide

theorem higherPrimitive_ne_zero : higherPrimitive ≠ 0 := by
  intro h
  have hd := detector_higherPrimitive
  rw [h, map_zero, map_zero] at hd
  exact zero_ne_one hd

/-- The actual reduced coproduct is the sum of the three presentation relations in tensor coordinates. -/
theorem primitiveEquation_higherPrimitive :
    ExteriorAlgebra.primitiveEquation R M (higherPrimitive : ExteriorAlgebra R M) =
      ExteriorAlgebra.ι R (m 0) ⊗ₜ[R] ExteriorAlgebra.ι R (nil 0 • m 1 + nil 1 • m 2) +
      ExteriorAlgebra.ι R (m 1) ⊗ₜ[R] ExteriorAlgebra.ι R (nil 0 • m 0 + nil 2 • m 2) +
      ExteriorAlgebra.ι R (m 2) ⊗ₜ[R] ExteriorAlgebra.ι R (nil 1 • m 0 + nil 2 • m 1) := by
  change ExteriorAlgebra.primitiveEquation R M
      (nil 0 • (wedge 0 1 : ExteriorAlgebra R M) +
        nil 1 • (wedge 0 2 : ExteriorAlgebra R M) +
        nil 2 • (wedge 1 2 : ExteriorAlgebra R M)) = _
  simp only [map_add, map_smul, wedge_coe, ExteriorAlgebra.primitiveEquation_ι_mul_ι,
    sub_eq_add_neg, neg_eq_self, smul_add, TensorProduct.tmul_add, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']
  have hmove (r : R) (x y : ExteriorAlgebra R M) :
      (r • x) ⊗ₜ[R] y = x ⊗ₜ[R] (r • y) := TensorProduct.smul_tmul r x y
  simp only [hmove]
  abel

/-- A nonzero primitive in degree two, proved using the actual exterior coproduct. -/
theorem higherPrimitive_isPrimitive :
    Coalgebra.IsSkewPrimitiveElem R (1 : ExteriorAlgebra R M) (1 : ExteriorAlgebra R M)
      (higherPrimitive : ExteriorAlgebra R M) := by
  apply (ExteriorAlgebra.primitiveEquation_eq_zero_iff R M _).mp
  rw [primitiveEquation_higherPrimitive, relation_zero, relation_one, relation_two, map_zero,
    TensorProduct.tmul_zero]
  simp

/-- This presentation cannot be free: the characteristic-free free-module theorem forbids its primitive. -/
theorem not_moduleFree : ¬ Module.Free R M := by
  intro h
  letI := h
  exact higherPrimitive_ne_zero
    (ExteriorAlgebra.primitive_homogeneous_eq_zero R M 2 (by decide)
      higherPrimitive higherPrimitive_isPrimitive)

end ChevalleyEilenbergCharacteristicTwoPrimitive
