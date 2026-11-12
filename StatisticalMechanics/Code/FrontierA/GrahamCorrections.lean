/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Ising.GHSVertexPartition

namespace StatMech.FrontierA

open Finset
open scoped symmDiff
open StatMech.Ising
open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]





def grahamPairSupport (x y : V) : Finset V := {x} ∆ {y}



def grahamFourSupport (i j k l : V) : Finset V :=
  grahamPairSupport i j ∆ grahamPairSupport k l



noncomputable def grahamTwoPoint (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (x y : V) : ℝ :=
  expJ E J (fun _ => 0) (spinProd (grahamPairSupport x y))


noncomputable def grahamFourPoint (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i j k l : V) : ℝ :=
  expJ E J (fun _ => 0) (spinProd (grahamFourSupport i j k l))


noncomputable def grahamUrsell4 (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i j k l : V) : ℝ :=
  grahamFourPoint E J i j k l
    - grahamTwoPoint E J i j * grahamTwoPoint E J k l
    - grahamTwoPoint E J i k * grahamTwoPoint E J j l
    - grahamTwoPoint E J i l * grahamTwoPoint E J j k

omit [Fintype V] in

@[simp] theorem grahamPairSupport_chain (i m k : V) :
    grahamPairSupport i m ∆ grahamPairSupport m k = grahamPairSupport i k := by
  classical
  ext x
  simp only [grahamPairSupport, Finset.mem_symmDiff, Finset.mem_singleton]
  tauto

omit [Fintype V] in

theorem spinProd_grahamPairSupport (s : ConfigSpace V) (x y : V) :
    spinProd (grahamPairSupport x y) s = spin s x * spin s y := by
  simpa [grahamPairSupport, spinProd] using
    (spinProd_mul_self ({x} : Finset V) ({y} : Finset V) s).symm

omit [Fintype V] in

theorem spinProd_grahamFourSupport (s : ConfigSpace V) (i j k l : V) :
    spinProd (grahamFourSupport i j k l) s =
      (spin s i * spin s j) * (spin s k * spin s l) := by
  rw [grahamFourSupport, ← spinProd_mul_self, spinProd_grahamPairSupport,
    spinProd_grahamPairSupport]


theorem grahamTwoPoint_eq_expJ (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (x y : V) :
    grahamTwoPoint E J x y =
      expJ E J (fun _ => 0) (fun s => spin s x * spin s y) := by
  unfold grahamTwoPoint
  congr 1
  funext s
  exact spinProd_grahamPairSupport s x y


theorem grahamFourPoint_eq_expJ (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i j k l : V) :
    grahamFourPoint E J i j k l =
      expJ E J (fun _ => 0)
        (fun s => (spin s i * spin s j) * (spin s k * spin s l)) := by
  unfold grahamFourPoint
  congr 1
  funext s
  exact spinProd_grahamFourSupport s i j k l



theorem grahamUrsell4_eq_expJ (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i j k l : V) :
    grahamUrsell4 E J i j k l =
      expJ E J (fun _ => 0)
          (fun s => (spin s i * spin s j) * (spin s k * spin s l))
        - expJ E J (fun _ => 0) (fun s => spin s i * spin s j) *
            expJ E J (fun _ => 0) (fun s => spin s k * spin s l)
        - expJ E J (fun _ => 0) (fun s => spin s i * spin s k) *
            expJ E J (fun _ => 0) (fun s => spin s j * spin s l)
        - expJ E J (fun _ => 0) (fun s => spin s i * spin s l) *
            expJ E J (fun _ => 0) (fun s => spin s j * spin s k) := by
  rw [grahamUrsell4, grahamFourPoint_eq_expJ,
    grahamTwoPoint_eq_expJ, grahamTwoPoint_eq_expJ,
    grahamTwoPoint_eq_expJ, grahamTwoPoint_eq_expJ,
    grahamTwoPoint_eq_expJ, grahamTwoPoint_eq_expJ]


@[simp] theorem grahamTwoPoint_self (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (x : V) : grahamTwoPoint E J x x = 1 := by
  classical
  unfold grahamTwoPoint
  rw [show grahamPairSupport x x = ∅ by simp [grahamPairSupport]]
  unfold expJ
  rw [show (∑ s : ConfigSpace V, spinProd ∅ s * wJ E J (fun _ => 0) s) =
      ZJ E J (fun _ => 0) by simp [spinProd, ZJ]]
  exact div_self (ZJ_pos E J (fun _ => 0)).ne'


theorem grahamTwoPoint_comm (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (x y : V) : grahamTwoPoint E J x y = grahamTwoPoint E J y x := by
  unfold grahamTwoPoint grahamPairSupport
  rw [symmDiff_comm]





noncomputable def grahamBridgeGap (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i k m : V) : ℝ :=
  grahamTwoPoint E J i k
    - grahamTwoPoint E J i m * grahamTwoPoint E J m k


theorem grahamBridgeGap_comm (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i k m : V) :
    grahamBridgeGap E J i k m = grahamBridgeGap E J k i m := by
  unfold grahamBridgeGap
  rw [grahamTwoPoint_comm E J i k, grahamTwoPoint_comm E J i m,
    grahamTwoPoint_comm E J m k]
  ring


noncomputable def grahamLeadingTerm (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i j k l m : V) : ℝ :=
  -2 * (grahamTwoPoint E J i m * grahamTwoPoint E J j m *
    grahamTwoPoint E J k m * grahamTwoPoint E J l m)


noncomputable def grahamKCorrection (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i j k l m : V) : ℝ :=
  -2 * (grahamBridgeGap E J i k m * grahamBridgeGap E J j k m *
    grahamTwoPoint E J k l)


noncomputable def grahamICorrection (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i j k l m : V) : ℝ :=
  -2 * (grahamTwoPoint E J i m * grahamTwoPoint E J j m *
    grahamBridgeGap E J i k m * grahamBridgeGap E J i l m)



noncomputable def grahamCorrectedRHS (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i j k l m : V) : ℝ :=
  grahamLeadingTerm E J i j k l m
    + grahamKCorrection E J i j k l m
    + grahamICorrection E J i j k l m


theorem grahamCorrectedRHS_eq (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i j k l m : V) :
    grahamCorrectedRHS E J i j k l m =
      -2 * (grahamTwoPoint E J i m * grahamTwoPoint E J j m *
        grahamTwoPoint E J k m * grahamTwoPoint E J l m)
      + -2 * (grahamBridgeGap E J i k m * grahamBridgeGap E J j k m *
        grahamTwoPoint E J k l)
      + -2 * (grahamTwoPoint E J i m * grahamTwoPoint E J j m *
        grahamBridgeGap E J i k m * grahamBridgeGap E J i l m) :=
  rfl


theorem grahamTwoPoint_nonneg (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (hJ : ∀ e ∈ E, 0 ≤ J e) (x y : V) :
    0 ≤ grahamTwoPoint E J x y := by
  exact ghsvp_expJ_zero_nonneg E J hJ (grahamPairSupport x y)


theorem grahamBridgeGap_nonneg (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (hJ : ∀ e ∈ E, 0 ≤ J e) (i k m : V) :
    0 ≤ grahamBridgeGap E J i k m := by
  rw [grahamBridgeGap, sub_nonneg]
  have h := gks_second_J E J (fun _ => 0) hJ (fun _ => le_rfl)
    (grahamPairSupport i m) (grahamPairSupport m k)
  rw [grahamPairSupport_chain] at h
  exact h


theorem grahamLeadingTerm_nonpos (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (hJ : ∀ e ∈ E, 0 ≤ J e) (i j k l m : V) :
    grahamLeadingTerm E J i j k l m ≤ 0 := by
  have hprod : 0 ≤ grahamTwoPoint E J i m * grahamTwoPoint E J j m *
      grahamTwoPoint E J k m * grahamTwoPoint E J l m :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (grahamTwoPoint_nonneg E J hJ i m)
          (grahamTwoPoint_nonneg E J hJ j m))
        (grahamTwoPoint_nonneg E J hJ k m))
      (grahamTwoPoint_nonneg E J hJ l m)
  unfold grahamLeadingTerm
  nlinarith


theorem grahamKCorrection_nonpos (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (hJ : ∀ e ∈ E, 0 ≤ J e) (i j k l m : V) :
    grahamKCorrection E J i j k l m ≤ 0 := by
  have hprod : 0 ≤ grahamBridgeGap E J i k m * grahamBridgeGap E J j k m *
      grahamTwoPoint E J k l :=
    mul_nonneg
      (mul_nonneg (grahamBridgeGap_nonneg E J hJ i k m)
        (grahamBridgeGap_nonneg E J hJ j k m))
      (grahamTwoPoint_nonneg E J hJ k l)
  unfold grahamKCorrection
  nlinarith


theorem grahamICorrection_nonpos (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (hJ : ∀ e ∈ E, 0 ≤ J e) (i j k l m : V) :
    grahamICorrection E J i j k l m ≤ 0 := by
  have hprod : 0 ≤ grahamTwoPoint E J i m * grahamTwoPoint E J j m *
      grahamBridgeGap E J i k m * grahamBridgeGap E J i l m :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (grahamTwoPoint_nonneg E J hJ i m)
          (grahamTwoPoint_nonneg E J hJ j m))
        (grahamBridgeGap_nonneg E J hJ i k m))
      (grahamBridgeGap_nonneg E J hJ i l m)
  unfold grahamICorrection
  nlinarith


theorem grahamCorrectedRHS_le_leading (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (hJ : ∀ e ∈ E, 0 ≤ J e) (i j k l m : V) :
    grahamCorrectedRHS E J i j k l m ≤ grahamLeadingTerm E J i j k l m := by
  have hk := grahamKCorrection_nonpos E J hJ i j k l m
  have hi := grahamICorrection_nonpos E J hJ i j k l m
  unfold grahamCorrectedRHS
  linarith


theorem grahamCorrectedRHS_nonpos (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (hJ : ∀ e ∈ E, 0 ≤ J e) (i j k l m : V) :
    grahamCorrectedRHS E J i j k l m ≤ 0 :=
  (grahamCorrectedRHS_le_leading E J hJ i j k l m).trans
    (grahamLeadingTerm_nonpos E J hJ i j k l m)



theorem grahamCorrectedRHS_aux_eq_l (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i j k l : V) :
    grahamCorrectedRHS E J i j k l l =
      -2 * (grahamTwoPoint E J i l * grahamTwoPoint E J j l *
        grahamTwoPoint E J k l)
      + -2 * (grahamBridgeGap E J i k l * grahamBridgeGap E J j k l *
        grahamTwoPoint E J k l) := by
  simp [grahamCorrectedRHS, grahamLeadingTerm, grahamKCorrection,
    grahamICorrection, grahamBridgeGap]

end StatMech.FrontierA
