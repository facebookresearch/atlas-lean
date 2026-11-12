/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationFormalMultiaffine
import Code.FrontierA.KacWardPolygonGlobalReduction
import Code.FrontierA.TriangularIsingSymbol
import Code.Sharpness.Simon












open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager



theorem ons_weightedRootIdentity_unconditional
    (L : Nat) [Fact (2 < L)] :
    ons_weightedRootIdentity L := by
  apply ons_weightedRootIdentity_of_decoratedFormal L
  apply ons_decoratedFormalKacWardIdentity_of_repeatedEdge_vanishes L
  intro a b m edge hrepeated
  exact ons_decFormalRoot_coeff_eq_zero_of_repeated
    L a b m edge hrepeated



noncomputable def squareTorusWeightedSpinScalePolynomial
    (L : Nat) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → Complex)
    (a b : Fin 2) : Polynomial Complex :=
  ∑ F ∈ evenSubgraphs (onsTorusGraph L),
    Polynomial.monomial F.card
      ((ons_spinCharacter a b (ons_evenHomology L F) : Complex) *
        ∏ edge ∈ F, weight edge)

theorem squareTorusWeightedSpinScalePolynomial_eval
    (L : Nat) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → Complex)
    (a b : Fin 2) (t : Complex) :
    (squareTorusWeightedSpinScalePolynomial L weight a b).eval t =
      ons_weightedSpinCharacterSum L (fun edge ↦ t * weight edge) a b := by
  classical
  unfold squareTorusWeightedSpinScalePolynomial
    ons_weightedSpinCharacterSum
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro F hF
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  ring

private theorem weightedPhase_scale
    (L : Nat) (weight : Sym2 (ZMod L × ZMod L) → Complex)
    (a b : Fin 2) (t : Complex) :
    ons_KWmatWeightedPhase L (fun edge ↦ t * weight edge) ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) =
      t • ons_KWmatWeightedPhase L weight ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) := by
  ext d₂ d₁
  simp only [ons_KWmatWeightedPhase, ons_KWmatWeighted,
    Matrix.smul_apply, smul_eq_mul]
  by_cases hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1
  · rw [if_pos hstep, if_pos hstep]
    ring
  · rw [if_neg hstep, if_neg hstep]
    simp



theorem squareTorus_weightedSpin_sq_eq_det
    (L : Nat) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → Complex)
    (a b : Fin 2) :
    ons_weightedSpinCharacterSum L weight a b ^ 2 =
      (1 - ons_KWmatWeightedPhase L weight ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)).det := by
  classical
  let M := ons_KWmatWeightedPhase L weight ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b)
  let P := kwDetScalePolynomial M
  let Q := (squareTorusWeightedSpinScalePolynomial L weight a b) ^ 2
  let card : Real := Fintype.card (ons_Dart L)
  let radius : Real := (2 * card ^ 2)⁻¹
  let B : Real := 1 + ∑ edge : Sym2 (ZMod L × ZMod L), ‖weight edge‖
  let delta : Real := radius / B
  have hcard : 0 < card := by
    dsimp only [card]
    exact_mod_cast Fintype.card_pos
  have hradius : 0 < radius := by
    dsimp only [radius]
    positivity
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  have hedgeB (edge : Sym2 (ZMod L × ZMod L)) : ‖weight edge‖ ≤ B := by
    dsimp only [B]
    have hsingle : ‖weight edge‖ ≤
        ∑ e : Sym2 (ZMod L × ZMod L), ‖weight e‖ :=
      Finset.single_le_sum (fun e _ ↦ norm_nonneg (weight e))
        (Finset.mem_univ edge)
    linarith
  have heval (r : Real) (hr : r ∈ Set.Ioo (0 : Real) delta) :
      P.eval (r : Complex) = Q.eval (r : Complex) := by
    let scaled : Sym2 (ZMod L × ZMod L) → Complex :=
      fun edge ↦ (r : Complex) * weight edge
    let q : Real := r * B
    have hq : 0 ≤ q := mul_nonneg hr.1.le hB.le
    have hscaled (edge : Sym2 (ZMod L × ZMod L)) :
        ‖scaled edge‖ ≤ q := by
      dsimp only [scaled, q]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
      exact mul_le_mul_of_nonneg_left (hedgeB edge) hr.1.le
    have hsmall : q < (2 * (Fintype.card (ons_Dart L) : Real) ^ 2)⁻¹ := by
      have := hr.2
      dsimp only [delta, radius, card] at this
      have hmul := (lt_div_iff₀ hB).mp this
      simpa only [q] using hmul
    have hroot := ons_weightedRootIdentity_unconditional L
      a b scaled q hq hscaled hsmall
    have hsquare := ons_KWmatWeightedPhase_detWalkRoot_sq
      L scaled a b q hq hscaled hsmall
    have hdet :
        (1 - ons_KWmatWeightedPhase L scaled ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)).det =
        ons_weightedSpinCharacterSum L scaled a b ^ 2 := by
      rw [← hsquare, hroot]
    dsimp only [P, Q]
    rw [kwDetScalePolynomial_eval, Polynomial.eval_pow,
      squareTorusWeightedSpinScalePolynomial_eval]
    rw [← weightedPhase_scale]
    exact hdet
  have hinfinite : Set.Infinite {z : Complex | P.eval z = Q.eval z} := by
    have hinterval : Set.Infinite (Set.Ioo (0 : Real) delta) :=
      Set.Ioo_infinite hdelta
    have himage : Set.Infinite
        ((fun r : Real ↦ (r : Complex)) '' Set.Ioo (0 : Real) delta) :=
      hinterval.image Complex.ofReal_injective.injOn
    apply himage.mono
    rintro z ⟨r, hr, rfl⟩
    exact heval r hr
  have hpoly : P = Q := Polynomial.eq_of_infinite_eval_eq P Q hinfinite
  have hone := congrArg (Polynomial.eval (1 : Complex)) hpoly
  dsimp only [P, Q] at hone
  rw [kwDetScalePolynomial_eval, Polynomial.eval_pow,
    squareTorusWeightedSpinScalePolynomial_eval] at hone
  simpa [M] using hone.symm




def squareTorusDirectionWeight (x y : Complex) (mu : Fin 4) : Complex :=
  match mu with
  | 0 => x
  | 1 => y
  | 2 => x
  | 3 => y



noncomputable def anisotropicSquareKWMatrixPhase
    (L : Nat) (x y omega u v : Complex) :
    Matrix (ons_Dart L) (ons_Dart L) Complex :=
  fun d₂ d₁ =>
    ons_dirPhase u v d₁.2 *
      if d₂.1 = ons_dirStep L d₁.2 d₁.1 then
        squareTorusDirectionWeight x y d₁.2 * ons_turnW omega d₁.2 d₂.2
      else 0


noncomputable def anisotropicSquareKWSymbolMatrix
    (x y omega z₁ z₂ : Complex) : Matrix (Fin 4) (Fin 4) Complex :=
  !![1 - x * z₁, -y * (-Complex.I * omega) * z₂,
        0, -y * omega * z₂⁻¹;
     -x * omega * z₁, 1 - y * z₂,
        -x * (-Complex.I * omega) * z₁⁻¹, 0;
     0, -y * omega * z₂, 1 - x * z₁⁻¹,
        -y * (-Complex.I * omega) * z₂⁻¹;
     -x * (-Complex.I * omega) * z₁, 0,
        -x * omega * z₁⁻¹, 1 - y * z₂⁻¹]


theorem anisotropicSquareKWSymbolMatrix_det
    (x y omega z₁ z₂ : Complex) (homega : omega ^ 2 = Complex.I)
    (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) :
    (anisotropicSquareKWSymbolMatrix x y omega z₁ z₂).det =
      (1 + x ^ 2) * (1 + y ^ 2) -
        x * (1 - y ^ 2) * (z₁ + z₁⁻¹) -
        y * (1 - x ^ 2) * (z₂ + z₂⁻¹) := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have homega4 : omega ^ 4 = -1 := by
    rw [show (4 : Nat) = 2 * 2 from rfl, pow_mul, homega, hI]
  have hI4 : Complex.I ^ 4 = 1 := by
    rw [show (4 : Nat) = 2 * 2 from rfl, pow_mul, hI]
    ring
  rw [anisotropicSquareKWSymbolMatrix, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.succAbove]
  field_simp [hz₁, hz₂]
  ring_nf
  rw [homega4, homega]
  ring_nf
  rw [hI4, hI]
  ring


noncomputable def anisotropicSquareHighTempSymbol
    (x y k₁ k₂ : Real) : Real :=
  (1 + x ^ 2) * (1 + y ^ 2) -
    2 * (x * (1 - y ^ 2) * Real.cos k₁ +
      y * (1 - x ^ 2) * Real.cos k₂)

theorem anisotropicSquareKWSymbolMatrix_det_cos
    (x y k₁ k₂ : Real) :
    (anisotropicSquareKWSymbolMatrix (x : Complex) (y : Complex)
      ons_turnRoot
      (Complex.exp (Complex.I * k₁))
      (Complex.exp (Complex.I * k₂))).det =
        (anisotropicSquareHighTempSymbol x y k₁ k₂ : Complex) := by
  have hcos : ∀ k : Real,
      Complex.exp (Complex.I * (k : Complex)) +
          Complex.exp (-(Complex.I * (k : Complex))) =
        2 * (Real.cos k : Complex) := by
    intro k
    rw [Complex.ofReal_cos, Complex.two_cos,
      mul_comm Complex.I (k : Complex), neg_mul]
  rw [anisotropicSquareKWSymbolMatrix_det]
  · rw [show (Complex.exp (Complex.I * (k₁ : Complex)))⁻¹ =
        Complex.exp (-(Complex.I * (k₁ : Complex))) from
      (Complex.exp_neg _).symm]
    rw [show (Complex.exp (Complex.I * (k₂ : Complex)))⁻¹ =
        Complex.exp (-(Complex.I * (k₂ : Complex))) from
      (Complex.exp_neg _).symm]
    rw [hcos k₁, hcos k₂]
    push_cast
    rw [← Complex.ofReal_cos, ← Complex.ofReal_cos]
    unfold anisotropicSquareHighTempSymbol
    norm_cast
    ring
  · exact ons_turnRoot_sq
  · exact Complex.exp_ne_zero _
  · exact Complex.exp_ne_zero _

noncomputable def anisotropicSquareKWBlockPhase
    (L : Nat) (x y omega u v : Complex)
    (g : ZMod L × ZMod L) : Matrix (Fin 4) (Fin 4) Complex :=
  fun a b ↦ anisotropicSquareKWMatrixPhase L x y omega u v (g, a) (0, b)

theorem anisotropicSquareKWMatrixPhase_translation_invariant
    (L : Nat) (x y omega u v : Complex)
    (t : ZMod L × ZMod L) (d₁ d₂ : ons_Dart L) :
    anisotropicSquareKWMatrixPhase L x y omega u v
        (ons_shiftDart L t d₂) (ons_shiftDart L t d₁) =
      anisotropicSquareKWMatrixPhase L x y omega u v d₂ d₁ := by
  unfold anisotropicSquareKWMatrixPhase ons_shiftDart
  simp only
  have hstep := ons_dirStep_shift L d₁.2 t d₁.1
  rw [hstep]
  have hiff :
      ((d₂.1.1 + t.1, d₂.1.2 + t.2) =
          ((ons_dirStep L d₁.2 d₁.1).1 + t.1,
            (ons_dirStep L d₁.2 d₁.1).2 + t.2)) ↔
        d₂.1 = ons_dirStep L d₁.2 d₁.1 := by
    rw [Prod.ext_iff, Prod.ext_iff]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨add_right_cancel h₁, add_right_cancel h₂⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨by rw [h₁], by rw [h₂]⟩
  by_cases hconnect : d₂.1 = ons_dirStep L d₁.2 d₁.1
  · rw [if_pos (hiff.mpr hconnect), if_pos hconnect]
  · rw [if_neg (fun h ↦ hconnect (hiff.mp h)), if_neg hconnect]

theorem anisotropicSquareKWMatrixPhase_eq_blockCirculant
    (L : Nat) (x y omega u v : Complex) :
    anisotropicSquareKWMatrixPhase L x y omega u v =
      ons_blockCirculant2D L 4
        (anisotropicSquareKWBlockPhase L x y omega u v) := by
  ext p q
  show anisotropicSquareKWMatrixPhase L x y omega u v p q =
    anisotropicSquareKWMatrixPhase L x y omega u v
      ((p.1.1 - q.1.1, p.1.2 - q.1.2), p.2) (0, q.2)
  have h := anisotropicSquareKWMatrixPhase_translation_invariant
    L x y omega u v q.1 (0, q.2)
      ((p.1.1 - q.1.1, p.1.2 - q.1.2), p.2)
  simpa [ons_shiftDart] using h

theorem anisotropicSquareKWBlockPhase_symbol
    (L : Nat) [NeZero L] [Fact (1 < L)]
    (x y omega u v root : Complex) (homega : omega ^ 2 = Complex.I)
    (hroot : IsPrimitiveRoot root L) (hu : u ≠ 0) (hv : v ≠ 0)
    (j : ZMod L × ZMod L) :
    ons_blockSymbol2D L 4 root
      (fun g ↦ (if g = 0 then (1 : Matrix (Fin 4) (Fin 4) Complex) else 0) -
        anisotropicSquareKWBlockPhase L x y omega u v g) j =
      anisotropicSquareKWSymbolMatrix x y omega
        (u * root ^ j.1.val) (v * root ^ j.2.val) := by
  have hrootne : root ≠ 0 := hroot.ne_zero (NeZero.ne L)
  have hval : (-1 : ZMod L).val + 1 = L := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne L)
    rw [ZMod.val_neg_one]
  have hbase : root ^ ((-1 : ZMod L).val) = root⁻¹ := by
    have hmul : root ^ ((-1 : ZMod L).val) * root = 1 := by
      rw [← pow_succ, hval, hroot.pow_eq_one]
    exact (inv_eq_of_mul_eq_one_left hmul).symm
  have hinv (m : Nat) : root ^ ((-1 : ZMod L).val * m) = (root ^ m)⁻¹ := by
    rw [pow_mul, hbase, inv_pow]
  ext a b
  simp only [ons_blockSymbol2D, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.sub_apply, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hid : (∑ k : ZMod L × ZMod L,
      root ^ (k.1.val * j.1.val + k.2.val * j.2.val) *
        (if k = 0 then (1 : Matrix (Fin 4) (Fin 4) Complex) else 0) a b) =
      (if a = b then 1 else 0 : Complex) := by
    rw [Finset.sum_eq_single (0 : ZMod L × ZMod L)]
    · simp [Matrix.one_apply]
    · intro k _ hk
      rw [if_neg hk]
      simp
    · exact fun h ↦ absurd (Finset.mem_univ _) h
  have hkw : (∑ k : ZMod L × ZMod L,
      root ^ (k.1.val * j.1.val + k.2.val * j.2.val) *
        anisotropicSquareKWBlockPhase L x y omega u v k a b) =
      root ^ ((ons_dirStep L b 0).1.val * j.1.val +
        (ons_dirStep L b 0).2.val * j.2.val) *
        (ons_dirPhase u v b *
          (squareTorusDirectionWeight x y b * ons_turnW omega b a)) := by
    have hentry (k : ZMod L × ZMod L) :
        anisotropicSquareKWBlockPhase L x y omega u v k a b =
          if k = ons_dirStep L b 0 then
            ons_dirPhase u v b *
              (squareTorusDirectionWeight x y b * ons_turnW omega b a)
          else 0 := by
      unfold anisotropicSquareKWBlockPhase anisotropicSquareKWMatrixPhase
      simp only [Prod.fst, Prod.snd]
      by_cases hk : k = ons_dirStep L b 0 <;> simp [hk]
    simp only [hentry]
    rw [Finset.sum_eq_single (ons_dirStep L b 0)]
    · rw [if_pos rfl]
    · intro k _ hk
      rw [if_neg hk, mul_zero]
    · exact fun h ↦ absurd (Finset.mem_univ _) h
  rw [hid, hkw]
  have homegane : omega ≠ 0 := by
    intro h
    rw [h] at homega
    simp at homega
    exact Complex.I_ne_zero homega.symm
  have hturn : omega⁻¹ = -Complex.I * omega := by
    apply inv_eq_of_mul_eq_one_left
    calc
      (-Complex.I * omega) * omega = -Complex.I * omega ^ 2 := by ring
      _ = 1 := by rw [homega, neg_mul, Complex.I_mul_I, neg_neg]
  fin_cases b <;>
    simp only [ons_dirStep, ons_dirPhase, squareTorusDirectionWeight] <;>
    fin_cases a <;>
    simp only [anisotropicSquareKWSymbolMatrix, ons_turnW,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.empty_val'] <;>
    simp_all [hinv, hturn, ZMod.val_one, one_mul, mul_one, mul_inv_rev] <;>
    field_simp <;> ring


theorem anisotropicSquareKWMatrixPhase_det
    (L : Nat) [NeZero L] [Fact (1 < L)]
    (x y omega u v root : Complex) (homega : omega ^ 2 = Complex.I)
    (hroot : IsPrimitiveRoot root L) (hu : u ≠ 0) (hv : v ≠ 0) :
    (1 - anisotropicSquareKWMatrixPhase L x y omega u v).det =
      ∏ j : ZMod L × ZMod L,
        ((1 + x ^ 2) * (1 + y ^ 2) -
          x * (1 - y ^ 2) *
            (u * root ^ j.1.val + (u * root ^ j.1.val)⁻¹) -
          y * (1 - x ^ 2) *
            (v * root ^ j.2.val + (v * root ^ j.2.val)⁻¹)) := by
  have hblock : (1 - anisotropicSquareKWMatrixPhase L x y omega u v) =
      ons_blockCirculant2D L 4
        (fun g ↦ (if g = 0 then (1 : Matrix (Fin 4) (Fin 4) Complex) else 0) -
          anisotropicSquareKWBlockPhase L x y omega u v g) := by
    rw [anisotropicSquareKWMatrixPhase_eq_blockCirculant]
    ext p q
    simp only [Matrix.sub_apply]
    unfold ons_blockCirculant2D
    simp only [Matrix.sub_apply]
    congr 1
    rw [Matrix.one_apply]
    by_cases hpq : p = q
    · subst p
      simp [Matrix.one_apply]
    · rw [if_neg hpq]
      by_cases hg : (p.1.1 - q.1.1, p.1.2 - q.1.2) = 0
      · rw [if_pos hg, Matrix.one_apply]
        have hdir : p.2 ≠ q.2 := by
          intro hdir
          apply hpq
          apply Prod.ext
          · apply Prod.ext <;> dsimp only at hg ⊢
            · exact sub_eq_zero.mp (congrArg Prod.fst hg)
            · exact sub_eq_zero.mp (congrArg Prod.snd hg)
          · exact hdir
        rw [if_neg hdir]
      · rw [if_neg hg]
        simp
  rw [hblock, ons_det_blockCirculant2D L 4 root hroot]
  apply Finset.prod_congr rfl
  intro j _
  rw [anisotropicSquareKWBlockPhase_symbol L x y omega u v root
    homega hroot hu hv j]
  exact anisotropicSquareKWSymbolMatrix_det x y omega _ _ homega
    (mul_ne_zero hu (pow_ne_zero _ (hroot.ne_zero (NeZero.ne L))))
    (mul_ne_zero hv (pow_ne_zero _ (hroot.ne_zero (NeZero.ne L))))



theorem anisotropicSquareKWMatrixPhase_det_eq_cosProduct
    (L : Nat) [NeZero L] [Fact (1 < L)]
    (x y : Complex) (a b : Fin 2) :
    (1 - anisotropicSquareKWMatrixPhase L x y ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)).det =
      ∏ j : ZMod L × ZMod L,
        ((1 + x ^ 2) * (1 + y ^ 2) -
          2 * x * (1 - y ^ 2) *
            Real.cos (2 * Real.pi *
              (j.1.val + (a.val : Real) / 2) / L) -
          2 * y * (1 - x ^ 2) *
            Real.cos (2 * Real.pi *
              (j.2.val + (b.val : Real) / 2) / L)) := by
  rw [anisotropicSquareKWMatrixPhase_det L x y ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) (ons_spaceRoot L)
    ons_turnRoot_sq (ons_spaceRoot_primitive L (NeZero.ne L))
    (ons_spinPhase_ne_zero L a) (ons_spinPhase_ne_zero L b)]
  apply Finset.prod_congr rfl
  intro j _
  rw [ons_spinPhase_spaceRoot_cos, ons_spinPhase_spaceRoot_cos]
  push_cast
  ring



def squareTorusHorizontalEdge (L : Nat)
    (edge : Sym2 (ZMod L × ZMod L)) : Prop :=
  ∃ p : ZMod L × ZMod L, edge = ons_portEdge L (p, 0)

noncomputable instance squareTorusHorizontalEdge_decidable (L : Nat)
    (edge : Sym2 (ZMod L × ZMod L)) :
    Decidable (squareTorusHorizontalEdge L edge) := Classical.dec _

noncomputable def anisotropicSquareEdgeWeight
    (L : Nat) (x y : Complex) : Sym2 (ZMod L × ZMod L) → Complex :=
  fun edge ↦ if squareTorusHorizontalEdge L edge then x else y

theorem anisotropicSquareEdgeWeight_port
    (L : Nat) [Fact (2 < L)] (x y : Complex) (d : ons_Dart L) :
    anisotropicSquareEdgeWeight L x y (ons_portEdge L d) =
      squareTorusDirectionWeight x y d.2 := by
  rcases d with ⟨p, mu⟩
  fin_cases mu
  · rw [anisotropicSquareEdgeWeight, if_pos]
    · rfl
    · exact ⟨p, rfl⟩
  · rw [anisotropicSquareEdgeWeight, if_neg]
    · rfl
    · rintro ⟨q, hq⟩
      have h := (ons_portEdge_eq_iff L (p, 1) (q, 0)).mp hq.symm
      rcases h with h | h
      · have := congrArg Prod.snd h
        norm_num at this
      · have := congrArg Prod.snd h
        simp [ons_dartRev] at this
  · rw [anisotropicSquareEdgeWeight, if_pos]
    · rfl
    · refine ⟨(p.1 - 1, p.2), ?_⟩
      exact ons_portEdge_west_eq_horizontal L p
  · rw [anisotropicSquareEdgeWeight, if_neg]
    · rfl
    · rintro ⟨q, hq⟩
      have h := (ons_portEdge_eq_iff L (p, 3) (q, 0)).mp hq.symm
      rcases h with h | h
      · have := congrArg Prod.snd h
        exact (by decide : (0 : Fin 4) ≠ 3) this
      · have := congrArg Prod.snd h
        simp [ons_dartRev] at this

theorem weightedPhase_anisotropicSquareEdgeWeight
    (L : Nat) [Fact (2 < L)] (x y omega u v : Complex) :
    ons_KWmatWeightedPhase L (anisotropicSquareEdgeWeight L x y)
        omega u v =
      anisotropicSquareKWMatrixPhase L x y omega u v := by
  ext d₂ d₁
  unfold ons_KWmatWeightedPhase ons_KWmatWeighted
    anisotropicSquareKWMatrixPhase
  rw [anisotropicSquareEdgeWeight_port]



theorem anisotropicSquare_weightedSpin_sq_eq_det
    (L : Nat) [Fact (2 < L)] (x y : Complex) (a b : Fin 2) :
    ons_weightedSpinCharacterSum L
        (anisotropicSquareEdgeWeight L x y) a b ^ 2 =
      (1 - anisotropicSquareKWMatrixPhase L x y ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)).det := by
  rw [← weightedPhase_anisotropicSquareEdgeWeight]
  exact squareTorus_weightedSpin_sq_eq_det L
    (anisotropicSquareEdgeWeight L x y) a b



theorem anisotropicSquare_weightedSpin_sq_eq_cosProduct
    (L : Nat) [Fact (2 < L)] (x y : Complex) (a b : Fin 2) :
    ons_weightedSpinCharacterSum L
        (anisotropicSquareEdgeWeight L x y) a b ^ 2 =
      ∏ j : ZMod L × ZMod L,
        ((1 + x ^ 2) * (1 + y ^ 2) -
          2 * x * (1 - y ^ 2) *
            Real.cos (2 * Real.pi *
              (j.1.val + (a.val : Real) / 2) / L) -
          2 * y * (1 - x ^ 2) *
            Real.cos (2 * Real.pi *
              (j.2.val + (b.val : Real) / 2) / L)) := by
  letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  rw [anisotropicSquare_weightedSpin_sq_eq_det]
  exact anisotropicSquareKWMatrixPhase_det_eq_cosProduct L x y a b

theorem anisotropicSquareFourierFactor_eq_triangularHighTempSymbol
    (J₁ J₂ k q : Real) :
    (1 + Real.tanh J₁ ^ 2) * (1 + Real.tanh J₂ ^ 2) -
        2 * Real.tanh J₁ * (1 - Real.tanh J₂ ^ 2) * Real.cos k -
        2 * Real.tanh J₂ * (1 - Real.tanh J₁ ^ 2) * Real.cos q =
      triangularIsingHighTempSymbol J₁ J₂ 0 k q := by
  simp only [triangularIsingHighTempSymbol, Real.tanh_zero, pow_two,
    mul_zero, zero_mul, add_zero, sub_zero]
  ring



theorem anisotropicSquare_weightedSpin_tanh_sq_eq_triangularProduct
    (L : Nat) [Fact (2 < L)] (J₁ J₂ : Real) (a b : Fin 2) :
    ons_weightedSpinCharacterSum L
        (anisotropicSquareEdgeWeight L (Real.tanh J₁) (Real.tanh J₂)) a b ^ 2 =
      ∏ j : ZMod L × ZMod L,
        (triangularIsingHighTempSymbol J₁ J₂ 0
          (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
          (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) : Complex) := by
  rw [anisotropicSquare_weightedSpin_sq_eq_cosProduct]
  apply Finset.prod_congr rfl
  intro j _
  norm_cast
  exact anisotropicSquareFourierFactor_eq_triangularHighTempSymbol
    J₁ J₂
    (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
    (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L)



theorem anisotropicSquare_normalizedSpin_tanh_sq_eq_triangularProduct
    (L : Nat) [Fact (2 < L)] (J₁ J₂ : Real) (a b : Fin 2) :
    (((Real.cosh J₁ * Real.cosh J₂) ^ (L * L) : Real) *
        ons_weightedSpinCharacterSum L
          (anisotropicSquareEdgeWeight L (Real.tanh J₁) (Real.tanh J₂)) a b) ^ 2 =
      ∏ j : ZMod L × ZMod L,
        (triangularIsingSymbol J₁ J₂ 0
          (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
          (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) : Complex) := by
  let C : Real := Real.cosh J₁ * Real.cosh J₂
  let W : Complex := ons_weightedSpinCharacterSum L
    (anisotropicSquareEdgeWeight L (Real.tanh J₁) (Real.tanh J₂)) a b
  have hW : W ^ 2 =
      ∏ j : ZMod L × ZMod L,
        (triangularIsingHighTempSymbol J₁ J₂ 0
          (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
          (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) : Complex) :=
    anisotropicSquare_weightedSpin_tanh_sq_eq_triangularProduct L J₁ J₂ a b
  have hfactor (j : ZMod L × ZMod L) :
      (triangularIsingSymbol J₁ J₂ 0
          (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
          (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) : Complex) =
        (C ^ 2 : Real) *
          triangularIsingHighTempSymbol J₁ J₂ 0
            (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
            (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) := by
    have hnorm := triangularIsingHighTempSymbol_mul_cosh_sq J₁ J₂ 0
      (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
      (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L)
    simp only [Real.cosh_zero, one_pow, mul_one] at hnorm
    have hreal :
        triangularIsingSymbol J₁ J₂ 0
            (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
            (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) =
          C ^ 2 * triangularIsingHighTempSymbol J₁ J₂ 0
            (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
            (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) := by
      rw [← hnorm]
      dsimp only [C]
      ring
    exact_mod_cast hreal
  change (((C ^ (L * L) : Real) : Complex) * W) ^ 2 = _
  rw [mul_pow, hW]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_prod, ZMod.card]
  push_cast
  have hpow : ((C : Complex) ^ (L * L)) ^ 2 =
      ((C : Complex) ^ 2) ^ (L * L) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  rw [hpow]




noncomputable def inhomogeneousEvenSubgraphSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → Real) : Real :=
  ∑ F ∈ evenSubgraphs G, ∏ edge ∈ F, weight edge



theorem inhomogeneousIsingPartition_highTemperature
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (coupling : Sym2 V → Real) :
    StatMech.Sharpness.ZJ G.edgeFinset coupling (fun _ ↦ 0) =
      (2 : Real) ^ Fintype.card V *
        (∏ edge ∈ G.edgeFinset, Real.cosh (coupling edge)) *
        inhomogeneousEvenSubgraphSum G (fun edge ↦ Real.tanh (coupling edge)) := by
  classical
  open StatMech.Sharpness in
  unfold ZJ
  have hweight (s : ConfigSpace V) :
      wJ G.edgeFinset coupling (fun _ ↦ 0) s =
        (∏ edge ∈ G.edgeFinset, Real.cosh (coupling edge)) *
          ∏ edge ∈ G.edgeFinset,
            (1 + Real.tanh (coupling edge) * bond s edge) := by
    unfold wJ
    simp only [zero_mul, Finset.sum_const_zero, add_zero]
    rw [Real.exp_sum, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro edge _
    exact exp_mul_eq_cosh_mul (coupling edge) (bond s edge)
      (bond_eq_one_or_neg_one s edge)
  simp_rw [hweight]
  have hexpand (s : ConfigSpace V) :
      (∏ edge ∈ G.edgeFinset,
          (1 + Real.tanh (coupling edge) * bond s edge)) =
        ∑ F ∈ G.edgeFinset.powerset,
          ∏ edge ∈ F, Real.tanh (coupling edge) * bond s edge :=
    Finset.prod_one_add _
  simp_rw [hexpand]
  rw [← Finset.mul_sum, Finset.sum_comm]
  unfold inhomogeneousEvenSubgraphSum
  rw [show (2 : Real) ^ Fintype.card V *
        (∏ edge ∈ G.edgeFinset, Real.cosh (coupling edge)) *
          ∑ F ∈ evenSubgraphs G,
            ∏ edge ∈ F, Real.tanh (coupling edge) =
      (∏ edge ∈ G.edgeFinset, Real.cosh (coupling edge)) *
        ((2 : Real) ^ Fintype.card V *
          ∑ F ∈ evenSubgraphs G,
            ∏ edge ∈ F, Real.tanh (coupling edge)) by ring]
  congr 1
  unfold evenSubgraphs
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro F hF
  rw [Finset.mem_powerset] at hF
  have hpull (s : ConfigSpace V) :
      (∏ edge ∈ F, Real.tanh (coupling edge) * bond s edge) =
        (∏ edge ∈ F, Real.tanh (coupling edge)) *
          ∏ edge ∈ F, bond s edge := by
    rw [Finset.prod_mul_distrib]
  simp_rw [hpull]
  rw [← Finset.mul_sum]
  have hnondiag : ∀ edge ∈ F, ¬ edge.IsDiag := by
    intro edge hedge
    exact SimpleGraph.not_isDiag_of_mem_edgeSet G
      (by rw [← SimpleGraph.mem_edgeFinset]; exact hF hedge)
  rw [sum_prod_bond_subgraph F hnondiag]
  by_cases heven : IsEvenSubgraph F
  · rw [if_pos heven, if_pos heven]
    ring
  · rw [if_neg heven, if_neg heven]
    ring

private theorem squareTorus_spinCharacter_arf_sum
    (h : Fin 2 × Fin 2) :
    (2 : Complex) =
      ons_spinCharacter 1 1 h + ons_spinCharacter 0 1 h +
        ons_spinCharacter 1 0 h - ons_spinCharacter 0 0 h := by
  rcases h with ⟨h₁, h₂⟩
  fin_cases h₁ <;> fin_cases h₂ <;>
    norm_num [ons_spinCharacter]


theorem two_mul_inhomogeneousEvenSubgraphSum_eq_spin
    (L : Nat) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → Real) :
    (2 : Complex) * inhomogeneousEvenSubgraphSum (onsTorusGraph L) weight =
      ons_weightedSpinCharacterSum L (fun edge ↦ (weight edge : Complex)) 1 1 +
      ons_weightedSpinCharacterSum L (fun edge ↦ (weight edge : Complex)) 0 1 +
      ons_weightedSpinCharacterSum L (fun edge ↦ (weight edge : Complex)) 1 0 -
      ons_weightedSpinCharacterSum L (fun edge ↦ (weight edge : Complex)) 0 0 := by
  classical
  unfold inhomogeneousEvenSubgraphSum ons_weightedSpinCharacterSum
  push_cast
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro F hF
  rw [squareTorus_spinCharacter_arf_sum (ons_evenHomology L F)]
  ring

end StatMech.FrontierA
