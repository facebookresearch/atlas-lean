/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib














open scoped BigOperators

set_option linter.unusedDecidableInType false

namespace StatMech.FrontierA

abbrev SurfaceBits (g : Nat) := Fin g → Fin 2
abbrev SurfaceHomology (g : Nat) := SurfaceBits g × SurfaceBits g
abbrev SurfaceSpinStructure (g : Nat) := SurfaceBits g × SurfaceBits g

def surfaceIntersection {g : Nat} (h k : SurfaceHomology g) : Fin 2 :=
  ∑ i, (h.1 i * k.2 i + h.2 i * k.1 i)

def surfaceQuadraticParity {g : Nat}
    (lambda : SurfaceSpinStructure g) (h : SurfaceHomology g) : Fin 2 :=
  ∑ i, (h.1 i * h.2 i + lambda.1 i * h.1 i + lambda.2 i * h.2 i)

def surfaceArfParity {g : Nat} (lambda : SurfaceSpinStructure g) : Fin 2 :=
  ∑ i, lambda.1 i * lambda.2 i

def surfaceParitySign (z : Fin 2) : Real := (-1 : Real) ^ z.val

@[simp] theorem surfaceParitySign_zero : surfaceParitySign 0 = 1 := by
  norm_num [surfaceParitySign]

theorem surfaceParitySign_add (z w : Fin 2) :
    surfaceParitySign (z + w) = surfaceParitySign z * surfaceParitySign w := by
  fin_cases z <;> fin_cases w <;> norm_num [surfaceParitySign, Fin.val_add]

theorem surfaceParitySign_finset_sum {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → Fin 2) :
    surfaceParitySign (∑ i ∈ S, f i) =
      ∏ i ∈ S, surfaceParitySign (f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi,
        surfaceParitySign_add, ih]

theorem surfaceParitySign_sum {g : Nat} (f : Fin g → Fin 2) :
    surfaceParitySign (∑ i, f i) = ∏ i, surfaceParitySign (f i) := by
  exact surfaceParitySign_finset_sum Finset.univ f

theorem surfaceQuadraticParity_local_add
    (a b x y x' y' : Fin 2) :
    (x + x') * (y + y') + a * (x + x') + b * (y + y') =
      (x * y + a * x + b * y) + (x' * y' + a * x' + b * y') +
        (x * y' + y * x') := by
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    fin_cases x' <;> fin_cases y' <;> decide

theorem surfaceQuadraticParity_add {g : Nat}
    (lambda : SurfaceSpinStructure g) (h k : SurfaceHomology g) :
    surfaceQuadraticParity lambda (h + k) =
      surfaceQuadraticParity lambda h + surfaceQuadraticParity lambda k +
        surfaceIntersection h k := by
  unfold surfaceQuadraticParity surfaceIntersection
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact surfaceQuadraticParity_local_add
    (lambda.1 i) (lambda.2 i) (h.1 i) (h.2 i) (k.1 i) (k.2 i)

def surfaceLocalArfQuadraticExponent
    (x y a b : Fin 2) : Fin 2 :=
  a * b + x * y + a * x + b * y

theorem surfaceLocalArfQuadratic_sum (x y : Fin 2) :
    (∑ ab : Fin 2 × Fin 2,
      surfaceParitySign (surfaceLocalArfQuadraticExponent x y ab.1 ab.2)) = 2 := by
  fin_cases x <;> fin_cases y <;>
    simp [Fin.sum_univ_two, Fintype.sum_prod_type,
      surfaceLocalArfQuadraticExponent, surfaceParitySign, Fin.val_add] <;>
    norm_num

theorem surfaceArf_add_quadratic_eq_sum_local {g : Nat}
    (lambda : SurfaceSpinStructure g) (h : SurfaceHomology g) :
    surfaceArfParity lambda + surfaceQuadraticParity lambda h =
      ∑ i, surfaceLocalArfQuadraticExponent
        (h.1 i) (h.2 i) (lambda.1 i) (lambda.2 i) := by
  unfold surfaceArfParity surfaceQuadraticParity surfaceLocalArfQuadraticExponent
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  abel

noncomputable def surfaceSpinFunctionEquiv (g : Nat) :
    SurfaceSpinStructure g ≃ (Fin g → Fin 2 × Fin 2) :=
  (Equiv.arrowProdEquivProdArrow (Fin g)
    (fun _ : Fin g => Fin 2) (fun _ : Fin g => Fin 2)).symm

@[simp] theorem surfaceSpinFunctionEquiv_apply_fst (g : Nat)
    (lambda : SurfaceSpinStructure g) (i : Fin g) :
    (surfaceSpinFunctionEquiv g lambda i).1 = lambda.1 i := rfl

@[simp] theorem surfaceSpinFunctionEquiv_apply_snd (g : Nat)
    (lambda : SurfaceSpinStructure g) (i : Fin g) :
    (surfaceSpinFunctionEquiv g lambda i).2 = lambda.2 i := rfl

theorem surface_arf_character_orthogonality (g : Nat)
    (h : SurfaceHomology g) :
    (∑ lambda : SurfaceSpinStructure g,
      surfaceParitySign
        (surfaceArfParity lambda + surfaceQuadraticParity lambda h)) =
      (2 : Real) ^ g := by
  calc
    (∑ lambda : SurfaceSpinStructure g,
        surfaceParitySign
          (surfaceArfParity lambda + surfaceQuadraticParity lambda h)) =
        ∑ f : Fin g → Fin 2 × Fin 2,
          ∏ i, surfaceParitySign
            (surfaceLocalArfQuadraticExponent
              (h.1 i) (h.2 i) (f i).1 (f i).2) := by
      apply Fintype.sum_equiv (surfaceSpinFunctionEquiv g)
      intro lambda
      rw [surfaceArf_add_quadratic_eq_sum_local, surfaceParitySign_sum]
      rfl
    _ = ∏ i : Fin g, ∑ ab : Fin 2 × Fin 2,
          surfaceParitySign
            (surfaceLocalArfQuadraticExponent
              (h.1 i) (h.2 i) ab.1 ab.2) :=
      (Fintype.prod_sum (fun i (ab : Fin 2 × Fin 2) =>
        surfaceParitySign (surfaceLocalArfQuadraticExponent
          (h.1 i) (h.2 i) ab.1 ab.2))).symm
    _ = (2 : Real) ^ g := by
      simp_rw [surfaceLocalArfQuadratic_sum]
      simp



noncomputable def surfaceTwistedSectorRoot {g : Nat}
    (weight : SurfaceHomology g → Real) (lambda : SurfaceSpinStructure g) : Real :=
  ∑ h : SurfaceHomology g,
    surfaceParitySign (surfaceQuadraticParity lambda h) * weight h


noncomputable def surfaceUnsignedSectorSum {g : Nat}
    (weight : SurfaceHomology g → Real) : Real :=
  ∑ h : SurfaceHomology g, weight h



theorem surface_arf_reconstruction_mul (g : Nat)
    (weight : SurfaceHomology g → Real) :
    (2 : Real) ^ g * surfaceUnsignedSectorSum weight =
      ∑ lambda : SurfaceSpinStructure g,
        surfaceParitySign (surfaceArfParity lambda) *
          surfaceTwistedSectorRoot weight lambda := by
  unfold surfaceUnsignedSectorSum surfaceTwistedSectorRoot
  calc
    (2 : Real) ^ g * ∑ h : SurfaceHomology g, weight h =
        ∑ h : SurfaceHomology g, (2 : Real) ^ g * weight h := by
      rw [Finset.mul_sum]
    _ = ∑ h : SurfaceHomology g,
        (∑ lambda : SurfaceSpinStructure g,
          surfaceParitySign
            (surfaceArfParity lambda + surfaceQuadraticParity lambda h)) *
            weight h := by
      apply Finset.sum_congr rfl
      intro h _
      rw [surface_arf_character_orthogonality]
    _ = ∑ h : SurfaceHomology g,
        ∑ lambda : SurfaceSpinStructure g,
          (surfaceParitySign (surfaceArfParity lambda) *
            surfaceParitySign (surfaceQuadraticParity lambda h)) * weight h := by
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro lambda _
      rw [surfaceParitySign_add]
    _ = ∑ lambda : SurfaceSpinStructure g,
        surfaceParitySign (surfaceArfParity lambda) *
          ∑ h : SurfaceHomology g,
            surfaceParitySign (surfaceQuadraticParity lambda h) * weight h := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro lambda _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring



theorem surface_arf_reconstruction (g : Nat)
    (weight : SurfaceHomology g → Real) :
    surfaceUnsignedSectorSum weight =
      ((2 : Real) ^ g)⁻¹ *
        ∑ lambda : SurfaceSpinStructure g,
          surfaceParitySign (surfaceArfParity lambda) *
            surfaceTwistedSectorRoot weight lambda := by
  rw [← surface_arf_reconstruction_mul]
  field_simp




noncomputable def surfaceTwistedSectorSquare {g : Nat}
    (weight : SurfaceHomology g → Real) (lambda : SurfaceSpinStructure g) : Real :=
  surfaceTwistedSectorRoot weight lambda ^ 2

@[simp] theorem surfaceTwistedSectorSquare_eq_sq {g : Nat}
    (weight : SurfaceHomology g → Real) (lambda : SurfaceSpinStructure g) :
    surfaceTwistedSectorSquare weight lambda =
      surfaceTwistedSectorRoot weight lambda ^ 2 := rfl

end StatMech.FrontierA
