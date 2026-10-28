/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact finite inverse-orbit certificates for literal original C322 positive source words. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3Hom
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationParabolicWords

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- A finite source word prefix and inverse orbit obey their exact original-generator recurrence. -/
def y322InverseWordOrbitChecked {size : ℕ} (word : Fin size → List (Fin 8))
    (parent : Fin size → Fin size) (generator : Fin size → Fin 8)
    (point : Fin 7 → ZMod 3) (orbit : Fin size → Fin 7 → ZMod 3) (i : Fin size) : Prop :=
  if i.val = 0 then word i = [] ∧ orbit i = point
  else (parent i).val < i.val ∧ word i = word (parent i) ++ [generator i] ∧
    orbit i = y322Orthogonal3Reflection (generator i) *ᵥ orbit (parent i)

/-- Literal source-word inverse-orbit checks are decidable over their finite coordinates. -/
instance y322InverseWordOrbitCheckedDecidable {size : ℕ} (word : Fin size → List (Fin 8))
    (parent : Fin size → Fin size) (generator : Fin size → Fin 8)
    (point : Fin 7 → ZMod 3) (orbit : Fin size → Fin 7 → ZMod 3) (i : Fin size) :
    Decidable (y322InverseWordOrbitChecked word parent generator point orbit i) := by
  unfold y322InverseWordOrbitChecked
  split <;> infer_instance

/-- Checked finite recurrences compute the inverse orbit of the actual original source words. -/
theorem y322InverseWordOrbit_checked_image {size : ℕ} (word : Fin size → List (Fin 8))
    (parent : Fin size → Fin size) (generator : Fin size → Fin 8)
    (point : Fin 7 → ZMod 3) (orbit : Fin size → Fin 7 → ZMod 3)
    (checked : ∀ i, y322InverseWordOrbitChecked word parent generator point orbit i)
    (i : Fin size) :
    (y322Orthogonal3Hom (y322PositiveWord (word i)))⁻¹.val *ᵥ point = orbit i := by
  induction i using (measure (fun i : Fin size => i.val)).wf.induction with
  | h i ih =>
    have hc := checked i
    by_cases hi : i.val = 0
    · simp only [y322InverseWordOrbitChecked, ite_eq_left hi] at hc
      rw [hc.1]
      simpa only [y322PositiveWord, List.map_nil, List.prod_nil, map_one, inv_one,
        Units.val_one, Matrix.one_mulVec] using hc.2.symm
    · simp only [y322InverseWordOrbitChecked, ite_eq_right hi] at hc
      have hs : y322PositiveWord [generator i] =
          (PresentedGroup.of (generator i) : Y322Presentation) := by
        simp only [y322PositiveWord, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one]
      rw [hc.2.1, y322PositiveWord_append, hs, map_mul,
        y322Orthogonal3Hom_generator, mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
      change y322Orthogonal3Reflection (generator i) *ᵥ
        ((y322Orthogonal3Hom (y322PositiveWord (word (parent i))))⁻¹.val *ᵥ point) = orbit i
      rw [ih (parent i) hc.1]
      exact hc.2.2.symm

/-- The same exact inverse source orbit holds for the standard finite column matrix action. -/
theorem y322InverseWordOrbit_checked_column {size : ℕ} (word : Fin size → List (Fin 8))
    (parent : Fin size → Fin size) (generator : Fin size → Fin 8)
    (point : Fin 7 → ZMod 3) (orbit : Fin size → Fin 7 → ZMod 3)
    (checked : ∀ i, y322InverseWordOrbitChecked word parent generator point orbit i)
    (i : Fin size) :
    (y322Orthogonal3Hom (y322PositiveWord (word i)))⁻¹ •
        Matrix.vecMulVec point (Pi.single (0 : Fin 7) 1) =
      Matrix.vecMulVec (orbit i) (Pi.single (0 : Fin 7) 1) := by
  change (y322Orthogonal3Hom (y322PositiveWord (word i)))⁻¹.val *
      Matrix.vecMulVec point (Pi.single (0 : Fin 7) 1) = _
  rw [Matrix.mul_vecMulVec, y322InverseWordOrbit_checked_image _ _ _ _ _ checked]

/-- Distinct finite orbit vectors have distinct standard column matrices. -/
theorem y322OrbitColumn_injective {size : ℕ} (orbit : Fin size → Fin 7 → ZMod 3)
    (hi : Function.Injective orbit) :
    Function.Injective (fun i => Matrix.vecMulVec (orbit i) (Pi.single (0 : Fin 7) 1)) := by
  intro i j hij
  apply hi
  have h := congrArg (fun m : Matrix (Fin 7) (Fin 7) (ZMod 3) => fun r => m r 0) hij
  simpa only [Matrix.vecMulVec_apply, Pi.single_eq_same, mul_one] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
