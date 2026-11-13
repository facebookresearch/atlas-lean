/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































































































import Mathlib

namespace StatMech.Universality

open Complex












noncomputable def isingLambda : ℂ := Complex.exp ((Real.pi / 4 : ℝ) * Complex.I)


theorem isingLambda_ne : isingLambda ≠ 0 := by
  unfold isingLambda; exact Complex.exp_ne_zero _


theorem isingLambda_sq : isingLambda ^ 2 = Complex.I := by
  unfold isingLambda
  rw [← Complex.exp_nat_mul,
      show (2 : ℕ) * ((Real.pi / 4 : ℝ) * Complex.I)
        = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp


theorem isingSqrt2_sq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  rw [show ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = (((Real.sqrt 2) ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Real.sq_sqrt (by norm_num)]
  norm_num


theorem isingSqrt2_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
  have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  exact_mod_cast this.ne'







theorem isingLambda_magic : isingLambda - isingLambda⁻¹ = Complex.I * (Real.sqrt 2 : ℂ) := by
  unfold isingLambda
  rw [← Complex.exp_neg,
      show -((Real.pi / 4 : ℝ) * Complex.I) = (-((Real.pi / 4 : ℝ) : ℂ)) * Complex.I by
        push_cast; ring]
  have hsin : Complex.sin ((Real.pi / 4 : ℝ) : ℂ) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sin, Real.sin_pi_div_four]
  have h := Complex.two_sin (((Real.pi / 4 : ℝ) : ℂ))
  have key : Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)
      - Complex.exp ((-((Real.pi / 4 : ℝ) : ℂ)) * Complex.I)
      = 2 * Complex.sin ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    rw [h]; ring_nf; rw [hI]; ring
  rw [key, hsin]; push_cast; ring


theorem sqrt2_mul_isingLambda : (Real.sqrt 2 : ℂ) * isingLambda = 1 + Complex.I := by
  unfold isingLambda
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := isingSqrt2_sq
  push_cast
  linear_combination (1 / 2 : ℂ) * hs + ((1 / 2 : ℂ) * Complex.I) * hs


theorem isingLambda_val : isingLambda = (1 + Complex.I) / (Real.sqrt 2 : ℂ) := by
  rw [eq_div_iff isingSqrt2_ne, mul_comm]; exact sqrt2_mul_isingLambda


theorem isingLambda_inv : isingLambda⁻¹ = (Real.sqrt 2 : ℂ) - isingLambda := by
  have h : isingLambda * ((Real.sqrt 2 : ℂ) - isingLambda) = 1 := by
    rw [mul_sub, mul_comm isingLambda (Real.sqrt 2 : ℂ), sqrt2_mul_isingLambda, ← sq,
        isingLambda_sq]
    ring
  symm
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h)












noncomputable def isingProj (e x : ℂ) : ℂ :=
  (1 / 2) * (x + (starRingEnd ℂ) e * (starRingEnd ℂ) x)


theorem isingProj_add (e x y : ℂ) :
    isingProj e (x + y) = isingProj e x + isingProj e y := by
  unfold isingProj
  rw [map_add]; ring






theorem isingProj_of_arg (e Fe : ℂ) (he : Complex.normSq e = 1)
    (harg : (starRingEnd ℂ) Fe = e * Fe) : isingProj e Fe = Fe := by
  unfold isingProj
  rw [harg, ← mul_assoc, ← Complex.normSq_eq_conj_mul_self, he]
  push_cast; ring






def IsSHolomorphic {ι : Type*} (f : ℂ → ℂ) (edges : ι → ℂ × ℂ × ℂ) : Prop :=
  ∀ i, isingProj (edges i).1 (f (edges i).2.1) = isingProj (edges i).1 (f (edges i).2.2)


































noncomputable def isingF : Fin 4 → ℂ → ℂ
  | 0 => fun X => X + X / (Real.sqrt 2 : ℂ)
  | 1 => fun X => isingLambda ^ 2 * X / (Real.sqrt 2 : ℂ)
  | 2 => fun X => isingLambda⁻¹ * X / (Real.sqrt 2 : ℂ)
  | 3 => fun X => isingLambda * X + isingLambda * X / (Real.sqrt 2 : ℂ)








theorem isingF_sHolo_relation (X : ℂ) :
    isingF 0 X + isingF 1 X = isingF 2 X + isingF 3 X := by
  show (X + X / (Real.sqrt 2 : ℂ)) + isingLambda ^ 2 * X / (Real.sqrt 2 : ℂ)
      = isingLambda⁻¹ * X / (Real.sqrt 2 : ℂ)
        + (isingLambda * X + isingLambda * X / (Real.sqrt 2 : ℂ))
  have hsne := isingSqrt2_ne
  rw [isingLambda_inv, isingLambda_sq, isingLambda_val]
  field_simp
  ring




theorem isingF_case1_relation :
    isingF 0 0 + isingF 1 0 = isingF 2 0 + isingF 3 0 := by
  simp only [isingF]
  ring









structure IsingMedialVertex where
  
  X : ℂ

namespace IsingMedialVertex

variable (D : IsingMedialVertex)


noncomputable def edgeObs (k : Fin 4) : ℂ := isingF k D.X




theorem sHolo_relation : D.edgeObs 0 + D.edgeObs 1 = D.edgeObs 2 + D.edgeObs 3 :=
  isingF_sHolo_relation D.X


theorem sHolo_sub_zero : D.edgeObs 0 + D.edgeObs 1 - D.edgeObs 2 - D.edgeObs 3 = 0 := by
  have h := D.sHolo_relation; linear_combination h











theorem contourCombination_zero :
    D.edgeObs 0 - D.edgeObs 1 + Complex.I * D.edgeObs 3 - Complex.I * D.edgeObs 2 = 0 := by
  show (D.X + D.X / (Real.sqrt 2 : ℂ)) - isingLambda ^ 2 * D.X / (Real.sqrt 2 : ℂ)
      + Complex.I * (isingLambda * D.X + isingLambda * D.X / (Real.sqrt 2 : ℂ))
      - Complex.I * (isingLambda⁻¹ * D.X / (Real.sqrt 2 : ℂ)) = 0
  have hsne := isingSqrt2_ne
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := isingSqrt2_sq
  rw [isingLambda_inv, isingLambda_sq, isingLambda_val]
  field_simp
  ring_nf
  linear_combination (D.X * (Real.sqrt 2 : ℂ) + 2 * D.X) * hI + (D.X - D.X * Complex.I) * hs

end IsingMedialVertex













noncomputable def isingContour (F : ℂ → ℂ) (z : Fin 4 → ℂ) : ℂ :=
  ∑ i : Fin 4, F ((z i + z (i + 1)) / 2) * (z (i + 1) - z i)



theorem isingContour_expand (F : ℂ → ℂ) (z : Fin 4 → ℂ) :
    isingContour F z =
      F ((z 0 + z 1) / 2) * (z 1 - z 0)
      + F ((z 1 + z 2) / 2) * (z 2 - z 1)
      + F ((z 2 + z 3) / 2) * (z 3 - z 2)
      + F ((z 3 + z 0) / 2) * (z 0 - z 3) := by
  unfold isingContour
  rw [Fin.sum_univ_four]
  rw [show ((0 : Fin 4) + 1) = 1 from rfl, show ((1 : Fin 4) + 1) = 2 from rfl,
      show ((2 : Fin 4) + 1) = 3 from rfl, show ((3 : Fin 4) + 1) = 0 from rfl]





noncomputable def isingFace (v d : ℂ) : Fin 4 → ℂ :=
  ![v + d, v + Complex.I * d, v - d, v - Complex.I * d]


theorem isingFace_midpoints (v d : ℂ) :
    ((isingFace v d 0 + isingFace v d 1) / 2 = v + (1 + Complex.I) / 2 * d) ∧
    ((isingFace v d 1 + isingFace v d 2) / 2 = v + (-1 + Complex.I) / 2 * d) ∧
    ((isingFace v d 2 + isingFace v d 3) / 2 = v + (-1 - Complex.I) / 2 * d) ∧
    ((isingFace v d 3 + isingFace v d 0) / 2 = v + (1 - Complex.I) / 2 * d) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [isingFace, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] <;> ring



theorem isingFace_edges (v d : ℂ) :
    (isingFace v d 1 - isingFace v d 0 = (Complex.I - 1) * d) ∧
    (isingFace v d 2 - isingFace v d 1 = (-1 - Complex.I) * d) ∧
    (isingFace v d 3 - isingFace v d 2 = (1 - Complex.I) * d) ∧
    (isingFace v d 0 - isingFace v d 3 = (1 + Complex.I) * d) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [isingFace, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] <;> ring








noncomputable def isingObservable (D : IsingMedialVertex) (v d : ℂ) : ℂ → ℂ := fun z =>
  if z = (isingFace v d 0 + isingFace v d 1) / 2 then D.edgeObs 0
  else if z = (isingFace v d 1 + isingFace v d 2) / 2 then D.edgeObs 3
  else if z = (isingFace v d 2 + isingFace v d 3) / 2 then D.edgeObs 1
  else if z = (isingFace v d 3 + isingFace v d 0) / 2 then D.edgeObs 2
  else 0








theorem isingContour_eq_combination (D : IsingMedialVertex) (v d : ℂ)
    (hpq : (isingFace v d 0 + isingFace v d 1) / 2 ≠ (isingFace v d 1 + isingFace v d 2) / 2)
    (hpr : (isingFace v d 0 + isingFace v d 1) / 2 ≠ (isingFace v d 2 + isingFace v d 3) / 2)
    (hps : (isingFace v d 0 + isingFace v d 1) / 2 ≠ (isingFace v d 3 + isingFace v d 0) / 2)
    (hqr : (isingFace v d 1 + isingFace v d 2) / 2 ≠ (isingFace v d 2 + isingFace v d 3) / 2)
    (hqs : (isingFace v d 1 + isingFace v d 2) / 2 ≠ (isingFace v d 3 + isingFace v d 0) / 2)
    (hrs : (isingFace v d 2 + isingFace v d 3) / 2 ≠ (isingFace v d 3 + isingFace v d 0) / 2) :
    isingContour (isingObservable D v d) (isingFace v d)
      = (Complex.I - 1) * d
          * (D.edgeObs 0 - D.edgeObs 1 + Complex.I * D.edgeObs 3 - Complex.I * D.edgeObs 2) := by
  rw [isingContour_expand]
  obtain ⟨e1, e2, e3, e4⟩ := isingFace_edges v d
  
  have h0 : isingObservable D v d ((isingFace v d 0 + isingFace v d 1) / 2) = D.edgeObs 0 := by
    unfold isingObservable; rw [if_pos rfl]
  have h1 : isingObservable D v d ((isingFace v d 1 + isingFace v d 2) / 2) = D.edgeObs 3 := by
    unfold isingObservable; rw [if_neg hpq.symm, if_pos rfl]
  have h2 : isingObservable D v d ((isingFace v d 2 + isingFace v d 3) / 2) = D.edgeObs 1 := by
    unfold isingObservable; rw [if_neg hpr.symm, if_neg hqr.symm, if_pos rfl]
  have h3 : isingObservable D v d ((isingFace v d 3 + isingFace v d 0) / 2) = D.edgeObs 2 := by
    unfold isingObservable; rw [if_neg hps.symm, if_neg hqs.symm, if_neg hrs.symm, if_pos rfl]
  rw [h0, h1, h2, h3, e1, e2, e3, e4]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  
  
  linear_combination (-(d * D.edgeObs 3 - d * D.edgeObs 2)) * hI



























theorem ising_sholo_face_relation (D : IsingMedialVertex) (v d : ℂ)
    (hpq : (isingFace v d 0 + isingFace v d 1) / 2 ≠ (isingFace v d 1 + isingFace v d 2) / 2)
    (hpr : (isingFace v d 0 + isingFace v d 1) / 2 ≠ (isingFace v d 2 + isingFace v d 3) / 2)
    (hps : (isingFace v d 0 + isingFace v d 1) / 2 ≠ (isingFace v d 3 + isingFace v d 0) / 2)
    (hqr : (isingFace v d 1 + isingFace v d 2) / 2 ≠ (isingFace v d 2 + isingFace v d 3) / 2)
    (hqs : (isingFace v d 1 + isingFace v d 2) / 2 ≠ (isingFace v d 3 + isingFace v d 0) / 2)
    (hrs : (isingFace v d 2 + isingFace v d 3) / 2 ≠ (isingFace v d 3 + isingFace v d 0) / 2) :
    isingContour (isingObservable D v d) (isingFace v d) = 0 := by
  rw [isingContour_eq_combination D v d hpq hpr hps hqr hqs hrs, D.contourCombination_zero,
      mul_zero]













theorem ising_sholo_closedContour
    {ι : Type*} (faces : Finset ι) (data : ι → IsingMedialVertex) (geo : ι → ℂ × ℂ)
    (hvanish : ∀ i ∈ faces,
      isingContour (isingObservable (data i) (geo i).1 (geo i).2)
        (isingFace (geo i).1 (geo i).2) = 0) :
    ∑ i ∈ faces,
      isingContour (isingObservable (data i) (geo i).1 (geo i).2)
        (isingFace (geo i).1 (geo i).2) = 0 :=
  Finset.sum_eq_zero hvanish














end StatMech.Universality
