/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Ising.GinibreBoundary

open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]



def inhomogeneousInteraction
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (h : V -> Real)
    (s : ConfigSpace V) : Real :=
  (∑ e ∈ E, J e * bond s e) + ∑ v : V, h v * spin s v



def scaledInhomogeneousPartition
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (h : V -> Real)
    (beta : Real) : Real :=
  ZJ E (fun e => beta * J e) (fun v => beta * h v)


def scaledMeanInteraction
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (h : V -> Real)
    (beta : Real) : Real :=
  expJ E (fun e => beta * J e) (fun v => beta * h v)
    (inhomogeneousInteraction E J h)


def boundaryInterfaceFreeEnergy
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hPlus h : V -> Real) (beta : Real) : Real :=
  Real.log (scaledInhomogeneousPartition E J hPlus beta) -
    Real.log (scaledInhomogeneousPartition E J h beta)

theorem scaled_wJ_eq_exp_interaction
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (h : V -> Real)
    (s : ConfigSpace V) (beta : Real) :
    wJ E (fun e => beta * J e) (fun v => beta * h v) s =
      Real.exp (beta * inhomogeneousInteraction E J h s) := by
  unfold wJ inhomogeneousInteraction
  congr 1
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro e _
    ring
  · apply Finset.sum_congr rfl
    intro v _
    ring

theorem hasDerivAt_scaled_wJ
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (h : V -> Real)
    (s : ConfigSpace V) (beta : Real) :
    HasDerivAt
      (fun b => wJ E (fun e => b * J e) (fun v => b * h v) s)
      (wJ E (fun e => beta * J e) (fun v => beta * h v) s *
        inhomogeneousInteraction E J h s) beta := by
  simp_rw [scaled_wJ_eq_exp_interaction]
  simpa using (Real.hasDerivAt_exp
    (beta * inhomogeneousInteraction E J h s)).comp beta
      ((hasDerivAt_id beta).mul_const (inhomogeneousInteraction E J h s))

theorem hasDerivAt_scaledInhomogeneousPartition
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (h : V -> Real)
    (beta : Real) :
    HasDerivAt (scaledInhomogeneousPartition E J h)
      (∑ s : ConfigSpace V,
        wJ E (fun e => beta * J e) (fun v => beta * h v) s *
          inhomogeneousInteraction E J h s) beta := by
  unfold scaledInhomogeneousPartition ZJ
  simpa using HasDerivAt.fun_sum (u := (Finset.univ : Finset (ConfigSpace V)))
    (fun s _ => hasDerivAt_scaled_wJ E J h s beta)

theorem hasDerivAt_log_scaledInhomogeneousPartition
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (h : V -> Real)
    (beta : Real) :
    HasDerivAt (fun b => Real.log (scaledInhomogeneousPartition E J h b))
      (scaledMeanInteraction E J h beta) beta := by
  have hderiv := hasDerivAt_scaledInhomogeneousPartition E J h beta
  have hpos : 0 < scaledInhomogeneousPartition E J h beta :=
    ZJ_pos E (fun e => beta * J e) (fun v => beta * h v)
  convert hderiv.log hpos.ne' using 1
  unfold scaledMeanInteraction expJ scaledInhomogeneousPartition
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  ring



theorem hasDerivAt_boundaryInterfaceFreeEnergy
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hPlus h : V -> Real) (beta : Real) :
    HasDerivAt (boundaryInterfaceFreeEnergy E J hPlus h)
      (scaledMeanInteraction E J hPlus beta -
        scaledMeanInteraction E J h beta) beta := by
  exact (hasDerivAt_log_scaledInhomogeneousPartition E J hPlus beta).sub
    (hasDerivAt_log_scaledInhomogeneousPartition E J h beta)

theorem expJ_add
    (E : Finset (Sym2 V)) (K : Sym2 V -> Real) (h : V -> Real)
    (f g : ConfigSpace V -> Real) :
    expJ E K h (fun s => f s + g s) = expJ E K h f + expJ E K h g := by
  unfold expJ
  rw [← add_div]
  congr 1
  simp_rw [add_mul]
  exact Finset.sum_add_distrib

theorem expJ_const_mul
    (E : Finset (Sym2 V)) (K : Sym2 V -> Real) (h : V -> Real)
    (c : Real) (f : ConfigSpace V -> Real) :
    expJ E K h (fun s => c * f s) = c * expJ E K h f := by
  unfold expJ
  rw [show (∑ s : ConfigSpace V, (c * f s) * wJ E K h s) =
      c * ∑ s : ConfigSpace V, f s * wJ E K h s by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring]
  ring

theorem expJ_sum
    {I : Type*} (E : Finset (Sym2 V)) (K : Sym2 V -> Real) (h : V -> Real)
    (S : Finset I) (f : I -> ConfigSpace V -> Real) :
    expJ E K h (fun s => ∑ i ∈ S, f i s) =
      ∑ i ∈ S, expJ E K h (f i) := by
  unfold expJ
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_div]



theorem scaledMeanInteraction_eq_bonds_add_fields
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (h : V -> Real)
    (beta : Real) :
    scaledMeanInteraction E J h beta =
      (∑ e ∈ E, J e *
        expJ E (fun a => beta * J a) (fun v => beta * h v)
          (fun s => bond s e)) +
      ∑ v : V, h v *
        expJ E (fun a => beta * J a) (fun x => beta * h x)
          (fun s => spin s v) := by
  unfold scaledMeanInteraction inhomogeneousInteraction
  rw [expJ_add,
    expJ_sum E (fun a => beta * J a) (fun v => beta * h v) E,
    expJ_sum E (fun a => beta * J a) (fun v => beta * h v) Finset.univ]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro e _
    exact expJ_const_mul E (fun a => beta * J a) (fun v => beta * h v)
      (J e) (fun s => bond s e)
  · apply Finset.sum_congr rfl
    intro v _
    exact expJ_const_mul E (fun a => beta * J a) (fun x => beta * h x)
      (h v) (fun s => spin s v)



theorem ginibre_boundary_fieldTerm_nonneg
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (hPlus h : V -> Real)
    (hJ : ∀ e ∈ E, 0 <= J e)
    (hdom : forall v, |h v| <= hPlus v)
    (beta : Real) (hbeta : 0 <= beta) (x : V) :
    0 <= hPlus x *
        expJ E (fun e => beta * J e) (fun v => beta * hPlus v)
          (fun s => spin s x) -
      h x * expJ E (fun e => beta * J e) (fun v => beta * h v)
        (fun s => spin s x) := by
  have hJbeta : ∀ e ∈ E, 0 <= beta * J e :=
    fun e he => mul_nonneg hbeta (hJ e he)
  have hdomBeta : forall v, |beta * h v| <= beta * hPlus v := by
    intro v
    rw [abs_mul, abs_of_nonneg hbeta]
    exact mul_le_mul_of_nonneg_left (hdom v) hbeta
  have hone := ginibre_boundary_abs_onePoint_le E
    (fun e => beta * J e) (fun v => beta * hPlus v)
    (fun v => beta * h v) hJbeta hdomBeta x
  have hhp : 0 <= hPlus x := (abs_nonneg (h x)).trans (hdom x)
  have hp : 0 <= expJ E (fun e => beta * J e) (fun v => beta * hPlus v)
      (fun s => spin s x) := (abs_nonneg _).trans hone
  have hle : h x * expJ E (fun e => beta * J e) (fun v => beta * h v)
        (fun s => spin s x) <=
      hPlus x * expJ E (fun e => beta * J e)
        (fun v => beta * hPlus v) (fun s => spin s x) := by
    calc
    h x * expJ E (fun e => beta * J e) (fun v => beta * h v)
        (fun s => spin s x) <=
        |h x * expJ E (fun e => beta * J e) (fun v => beta * h v)
          (fun s => spin s x)| := le_abs_self _
    _ = |h x| * |expJ E (fun e => beta * J e) (fun v => beta * h v)
          (fun s => spin s x)| := abs_mul _ _
    _ <= hPlus x * expJ E (fun e => beta * J e)
          (fun v => beta * hPlus v) (fun s => spin s x) := by
      exact mul_le_mul (hdom x) hone (abs_nonneg _) hhp
  linarith
  



theorem boundaryInterfaceFreeEnergy_deriv_nonneg
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (hPlus h : V -> Real)
    (hJ : ∀ e ∈ E, 0 <= J e)
    (hdom : forall v, |h v| <= hPlus v)
    (beta : Real) (hbeta : 0 <= beta) :
    0 <= deriv (boundaryInterfaceFreeEnergy E J hPlus h) beta := by
  rw [(hasDerivAt_boundaryInterfaceFreeEnergy E J hPlus h beta).deriv]
  rw [scaledMeanInteraction_eq_bonds_add_fields,
    scaledMeanInteraction_eq_bonds_add_fields]
  rw [add_sub_add_comm]
  apply add_nonneg
  · rw [← Finset.sum_sub_distrib]
    apply Finset.sum_nonneg
    intro e he
    rw [← mul_sub]
    apply mul_nonneg (hJ e he)
    have hJbeta : ∀ a ∈ E, 0 <= beta * J a :=
      fun a ha => mul_nonneg hbeta (hJ a ha)
    have hdomBeta : forall v, |beta * h v| <= beta * hPlus v := by
      intro v
      rw [abs_mul, abs_of_nonneg hbeta]
      exact mul_le_mul_of_nonneg_left (hdom v) hbeta
    exact sub_nonneg.mpr (ginibre_boundary_bond_mono E
      (fun a => beta * J a) (fun v => beta * hPlus v)
      (fun v => beta * h v) hJbeta hdomBeta e)
  · rw [← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun v _ =>
      ginibre_boundary_fieldTerm_nonneg E J hPlus h hJ hdom beta hbeta v

end

end StatMech.Ising
