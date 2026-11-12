/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.FinitePlusTailContraction











namespace StatMech
namespace Exact3D

namespace FinitePlusTailState

variable {n : ℕ} {α : Type*}


def origin : FinitePlusTailState n α where
  finite := 0
  tail := 0


noncomputable def mixedNorm (x : FinitePlusTailState n α) : ℝ :=
  x.dist (origin : FinitePlusTailState n α)



def ThermalStableCone (η t : ℝ) (s : FinitePlusTailState n α) : Prop :=
  mixedNorm s ≤ η * |t|


theorem mixedNorm_nonneg (x : FinitePlusTailState n α) :
    0 ≤ mixedNorm x :=
  dist_nonneg x origin

end FinitePlusTailState

namespace FinitePlusTailLipschitzCertificate

variable {n : ℕ} {α : Type*}


theorem mixedNorm_map_le_mul_of_map_origin
    (C : FinitePlusTailLipschitzCertificate n α)
    (h0 :
      C.map (FinitePlusTailState.origin : FinitePlusTailState n α) =
        FinitePlusTailState.origin)
    (x : FinitePlusTailState n α) :
    FinitePlusTailState.mixedNorm (C.map x) ≤
      C.c * FinitePlusTailState.mixedNorm x := by
  simpa [FinitePlusTailState.mixedNorm, h0] using
    C.mixed_lipschitz x
      (FinitePlusTailState.origin : FinitePlusTailState n α)


theorem map_mem_thermalStableCone_of_c_le_abs_thermal
    (C : FinitePlusTailLipschitzCertificate n α)
    (h0 :
      C.map (FinitePlusTailState.origin : FinitePlusTailState n α) =
        FinitePlusTailState.origin)
    {thermal η t : ℝ} {s : FinitePlusTailState n α}
    (hη : 0 ≤ η)
    (hdom : C.c ≤ |thermal|)
    (hs : FinitePlusTailState.ThermalStableCone η t s) :
    FinitePlusTailState.ThermalStableCone η (thermal * t) (C.map s) := by
  have hcone_rhs_nonneg : 0 ≤ η * |t| :=
    mul_nonneg hη (abs_nonneg _)
  calc
    FinitePlusTailState.mixedNorm (C.map s) ≤
        C.c * FinitePlusTailState.mixedNorm s :=
      C.mixedNorm_map_le_mul_of_map_origin h0 s
    _ ≤ C.c * (η * |t|) :=
      mul_le_mul_of_nonneg_left hs C.c_nonneg
    _ ≤ |thermal| * (η * |t|) :=
      mul_le_mul_of_nonneg_right hdom hcone_rhs_nonneg
    _ = η * |thermal * t| := by
      rw [abs_mul]
      ring


theorem iterate_origin_of_map_origin
    (C : FinitePlusTailLipschitzCertificate n α)
    (h0 :
      C.map (FinitePlusTailState.origin : FinitePlusTailState n α) =
        FinitePlusTailState.origin)
    (k : ℕ) :
    C.iterate k
        (FinitePlusTailState.origin : FinitePlusTailState n α) =
      FinitePlusTailState.origin := by
  induction k with
  | zero =>
      simp [iterate]
  | succ k ih =>
      simp [iterate, ih, h0]



theorem iterate_mem_thermalStableCone_of_c_le_abs_thermal
    (C : FinitePlusTailLipschitzCertificate n α)
    (h0 :
      C.map (FinitePlusTailState.origin : FinitePlusTailState n α) =
        FinitePlusTailState.origin)
    {thermal η t : ℝ} {s : FinitePlusTailState n α}
    (hη : 0 ≤ η)
    (hdom : C.c ≤ |thermal|)
    (hs : FinitePlusTailState.ThermalStableCone η t s)
    (k : ℕ) :
    FinitePlusTailState.ThermalStableCone η (thermal ^ k * t)
      (C.iterate k s) := by
  induction k with
  | zero =>
      simpa [iterate] using hs
  | succ k ih =>
      have hstep :=
        C.map_mem_thermalStableCone_of_c_le_abs_thermal
          h0 hη hdom ih
      simpa [iterate, pow_succ', mul_assoc] using hstep

end FinitePlusTailLipschitzCertificate





structure FinitePlusTailHyperbolicSplitting (n : ℕ) (α : Type*) where
  thermal : ℝ
  thermal_gt_one : 1 < thermal
  stable : FinitePlusTailLipschitzCertificate n α
  stable_origin :
    stable.map (FinitePlusTailState.origin : FinitePlusTailState n α) =
      FinitePlusTailState.origin
  stable_dominated : stable.c ≤ |thermal|

namespace FinitePlusTailHyperbolicSplitting

variable {n : ℕ} {α : Type*}



abbrev State (n : ℕ) (α : Type*) :=
  ℝ × FinitePlusTailState n α


def origin : State n α :=
  (0, FinitePlusTailState.origin)



noncomputable def step (H : FinitePlusTailHyperbolicSplitting n α)
    (x : State n α) : State n α :=
  (H.thermal * x.1, H.stable.map x.2)


noncomputable def iterate (H : FinitePlusTailHyperbolicSplitting n α) :
    ℕ → State n α → State n α
  | 0, x => x
  | k + 1, x => H.step (H.iterate k x)


theorem step_origin (H : FinitePlusTailHyperbolicSplitting n α) :
    H.step origin = origin := by
  apply Prod.ext
  · simp [step, origin]
  · simpa [step, origin] using H.stable_origin


theorem iterate_origin (H : FinitePlusTailHyperbolicSplitting n α) (k : ℕ) :
    H.iterate k origin = origin := by
  induction k with
  | zero =>
      simp [iterate]
  | succ k ih =>
      simp [iterate, ih, H.step_origin]



theorem iterate_fst_eq
    (H : FinitePlusTailHyperbolicSplitting n α)
    (k : ℕ) (x : State n α) :
    (H.iterate k x).1 = H.thermal ^ k * x.1 := by
  induction k with
  | zero =>
      simp [iterate]
  | succ k ih =>
      simp [iterate, step, ih, pow_succ', mul_assoc]


theorem iterate_snd_eq
    (H : FinitePlusTailHyperbolicSplitting n α)
    (k : ℕ) (x : State n α) :
    (H.iterate k x).2 = H.stable.iterate k x.2 := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      calc
        (H.iterate (k + 1) x).2 =
            (H.step (H.iterate k x)).2 := rfl
        _ = H.stable.map (H.iterate k x).2 := rfl
        _ = H.stable.map (H.stable.iterate k x.2) := by
          rw [ih]
        _ = H.stable.iterate (k + 1) x.2 := rfl


def cone (_H : FinitePlusTailHyperbolicSplitting n α)
    (η : ℝ) (x : State n α) : Prop :=
  FinitePlusTailState.ThermalStableCone η x.1 x.2


theorem cone_step
    (H : FinitePlusTailHyperbolicSplitting n α)
    {η : ℝ} (hη : 0 ≤ η) {x : State n α}
    (hx : H.cone η x) :
    H.cone η (H.step x) := by
  change
    FinitePlusTailState.ThermalStableCone η
      (H.thermal * x.1) (H.stable.map x.2)
  change FinitePlusTailState.ThermalStableCone η x.1 x.2 at hx
  exact
    H.stable.map_mem_thermalStableCone_of_c_le_abs_thermal
      H.stable_origin hη H.stable_dominated hx


theorem cone_iterate
    (H : FinitePlusTailHyperbolicSplitting n α)
    {η : ℝ} (hη : 0 ≤ η) {x : State n α}
    (hx : H.cone η x) (k : ℕ) :
    H.cone η (H.iterate k x) := by
  change
    FinitePlusTailState.ThermalStableCone η
      (H.iterate k x).1 (H.iterate k x).2
  change FinitePlusTailState.ThermalStableCone η x.1 x.2 at hx
  rw [H.iterate_fst_eq k x, H.iterate_snd_eq k x]
  exact
    H.stable.iterate_mem_thermalStableCone_of_c_le_abs_thermal
      H.stable_origin hη H.stable_dominated hx k

end FinitePlusTailHyperbolicSplitting



structure FinitePlusTailConeCertificate (n : ℕ) (α : Type*) where
  contraction : FinitePlusTailLipschitzCertificate n α
  thermal : FinitePlusTailState n α → ℝ
  stableSize : FinitePlusTailState n α → ℝ
  thermalMultiplier : ℝ
  stableStepConstant : ℝ
  stableSize_nonneg : ∀ x, 0 ≤ stableSize x
  stableStepConstant_nonneg : 0 ≤ stableStepConstant
  thermal_step :
    ∀ x, thermal (contraction.map x) = thermalMultiplier * thermal x
  stable_step_bound :
    ∀ x,
      stableSize (contraction.map x) ≤
        stableStepConstant * stableSize x
  stable_dominated : stableStepConstant ≤ |thermalMultiplier|

namespace FinitePlusTailConeCertificate

variable {n : ℕ} {α : Type*}



def cone (C : FinitePlusTailConeCertificate n α)
    (η : ℝ) (x : FinitePlusTailState n α) : Prop :=
  C.stableSize x ≤ η * |C.thermal x|


theorem cone_step
    (C : FinitePlusTailConeCertificate n α)
    {η : ℝ} (hη : 0 ≤ η) {x : FinitePlusTailState n α}
    (hx : C.cone η x) :
    C.cone η (C.contraction.map x) := by
  have hcone_rhs_nonneg : 0 ≤ η * |C.thermal x| :=
    mul_nonneg hη (abs_nonneg _)
  calc
    C.stableSize (C.contraction.map x) ≤
        C.stableStepConstant * C.stableSize x :=
      C.stable_step_bound x
    _ ≤ C.stableStepConstant * (η * |C.thermal x|) :=
      mul_le_mul_of_nonneg_left hx C.stableStepConstant_nonneg
    _ ≤ |C.thermalMultiplier| * (η * |C.thermal x|) :=
      mul_le_mul_of_nonneg_right C.stable_dominated hcone_rhs_nonneg
    _ = η * |C.thermal (C.contraction.map x)| := by
      rw [C.thermal_step x, abs_mul]
      ring



theorem thermal_iterate_eq
    (C : FinitePlusTailConeCertificate n α)
    (k : ℕ) (x : FinitePlusTailState n α) :
    C.thermal (C.contraction.iterate k x) =
      C.thermalMultiplier ^ k * C.thermal x := by
  induction k with
  | zero =>
      simp [FinitePlusTailLipschitzCertificate.iterate]
  | succ k ih =>
      calc
        C.thermal (C.contraction.iterate (k + 1) x) =
            C.thermal (C.contraction.map (C.contraction.iterate k x)) := rfl
        _ =
            C.thermalMultiplier *
              C.thermal (C.contraction.iterate k x) :=
          C.thermal_step (C.contraction.iterate k x)
        _ =
            C.thermalMultiplier *
              (C.thermalMultiplier ^ k * C.thermal x) := by
          rw [ih]
        _ =
            C.thermalMultiplier ^ (k + 1) * C.thermal x := by
          rw [pow_succ']
          ring


theorem stableSize_iterate_le
    (C : FinitePlusTailConeCertificate n α)
    (k : ℕ) (x : FinitePlusTailState n α) :
    C.stableSize (C.contraction.iterate k x) ≤
      C.stableStepConstant ^ k * C.stableSize x := by
  induction k with
  | zero =>
      simp [FinitePlusTailLipschitzCertificate.iterate]
  | succ k ih =>
      calc
        C.stableSize (C.contraction.iterate (k + 1) x) =
            C.stableSize
              (C.contraction.map (C.contraction.iterate k x)) := rfl
        _ ≤
            C.stableStepConstant *
              C.stableSize (C.contraction.iterate k x) :=
          C.stable_step_bound (C.contraction.iterate k x)
        _ ≤
            C.stableStepConstant *
              (C.stableStepConstant ^ k * C.stableSize x) :=
          mul_le_mul_of_nonneg_left ih C.stableStepConstant_nonneg
        _ =
            C.stableStepConstant ^ (k + 1) * C.stableSize x := by
          rw [pow_succ']
          ring


theorem cone_iterate
    (C : FinitePlusTailConeCertificate n α)
    {η : ℝ} (hη : 0 ≤ η) {x : FinitePlusTailState n α}
    (hx : C.cone η x) (k : ℕ) :
    C.cone η (C.contraction.iterate k x) := by
  induction k with
  | zero =>
      simpa [FinitePlusTailLipschitzCertificate.iterate] using hx
  | succ _ ih =>
      exact C.cone_step hη ih


theorem cone_iterate_closed_form
    (C : FinitePlusTailConeCertificate n α)
    {η : ℝ} (hη : 0 ≤ η) {x : FinitePlusTailState n α}
    (hx : C.cone η x) (k : ℕ) :
    C.stableSize (C.contraction.iterate k x) ≤
      η * |C.thermalMultiplier ^ k * C.thermal x| := by
  have hcone := C.cone_iterate hη hx k
  simpa [cone, C.thermal_iterate_eq k x] using hcone

end FinitePlusTailConeCertificate

end Exact3D
end StatMech
