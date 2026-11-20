/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptiveConnectorPhase
import Code.FrontierA.KacWardAdaptiveIdealPhaseHomotopy
import Code.FrontierA.KacWardRectilinearHomotopyReduction





namespace StatMech.FrontierA

open scoped BigOperators

private theorem fintype_prod_eq_two_factors
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℂ) (a b : ι) (hab : a ≠ b)
    (hone : ∀ x, x ≠ a → x ≠ b → f x = 1) :
    (∏ x, f x) = f a * f b := by
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ a)]
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem
    (show b ∈ Finset.univ \ {a} by simp [hab.symm])]
  have hrest : ∏ x ∈ (Finset.univ \ {a}) \ {b}, f x = 1 := by
    apply Finset.prod_eq_one
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton,
      true_and] at hx
    exact hone x hx.1 hx.2
  rw [hrest]
  ring

private theorem kwVectorTurnPhase_eq_one_of_eq {x y : ℂ} (h : x = y) :
    kwVectorTurnPhase x y = 1 := by
  subst y
  simp [kwVectorTurnPhase, kwAngleTurnPhase]

private theorem kwVectorTurnPhase_pos_left
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    kwVectorTurnPhase (s * z) w = kwVectorTurnPhase (t * z) w := by
  calc
    kwVectorTurnPhase (s * z) w = kwVectorTurnPhase z w := by
      convert kwVectorTurnPhase_pos_scales s 1 hs (by norm_num) z w hz hw <;>
        norm_num
    _ = kwVectorTurnPhase (t * z) w := by
      symm
      convert kwVectorTurnPhase_pos_scales t 1 ht (by norm_num) z w hz hw <;>
        norm_num

private theorem kwVectorTurnPhase_pos_right
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    kwVectorTurnPhase z (s * w) = kwVectorTurnPhase z (t * w) := by
  calc
    kwVectorTurnPhase z (s * w) = kwVectorTurnPhase z w := by
      convert kwVectorTurnPhase_pos_scales 1 s (by norm_num) hs z w hz hw <;>
        norm_num
    _ = kwVectorTurnPhase z (t * w) := by
      symm
      convert kwVectorTurnPhase_pos_scales 1 t (by norm_num) ht z w hz hw <;>
        norm_num

set_option maxHeartbeats 800000 in

theorem KWAdaptivePatchedData.ideal_block_phase
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (hcross : ∀ i : Fin n, kwComplexCross (polygon.edgeVector i)
      (polygon.edgeVector (i + 1)) ≠ 0)
    (i : Fin n) :
    (∏ l : Fin (2 * (M + 1)),
        kwVectorTurnPhase
          (kwRawEdge patch.idealVertex (finProdFinEquiv (i, l)))
          (kwRawEdge patch.idealVertex (finProdFinEquiv (i, l) + 1))) =
      kwVectorTurnPhase (polygon.edgeVector i)
        (polygon.edgeVector (i + 1)) := by
  let F : Fin (2 * (M + 1)) → ℂ := fun l ↦
    kwVectorTurnPhase
      (kwRawEdge patch.idealVertex (finProdFinEquiv (i, l)))
      (kwRawEdge patch.idealVertex (finProdFinEquiv (i, l) + 1))
  let G : Fin (M + 1) → ℂ := fun k ↦
    F (kwStairEvenLocal k) * F (kwStairOddLocal k)
  have hreindex : (∏ l : Fin (2 * (M + 1)), F l) = ∏ k, G k := by
    let e : Fin (M + 1) × Fin 2 ≃ Fin (2 * (M + 1)) :=
      (finProdFinEquiv (m := M + 1) (n := 2)).trans
        (finCongr (by ring))
    calc
      (∏ l, F l) = ∏ p : Fin (M + 1) × Fin 2, F (e p) := by
        exact (Fintype.prod_equiv e _ _ fun _ ↦ rfl).symm
      _ = ∏ k, G k := by
        rw [Fintype.prod_prod_type]
        apply Fintype.prod_congr
        intro k
        rw [show (∏ r : Fin 2, F (e (k, r))) =
            F (kwStairEvenLocal k) * F (kwStairOddLocal k) by
          rw [Fin.prod_univ_two]
          congr 1 <;> apply congrArg F <;> apply Fin.ext <;>
            simp [e, finProdFinEquiv, kwStairEvenLocal,
              kwStairOddLocal] <;> omega]
  rw [show (∏ l, kwVectorTurnPhase
      (kwRawEdge patch.idealVertex (finProdFinEquiv (i, l)))
      (kwRawEdge patch.idealVertex (finProdFinEquiv (i, l) + 1))) =
      ∏ l, F l by rfl, hreindex]
  let first : Fin (M + 1) := patch.lastMiddleIndex.castSucc
  let last : Fin (M + 1) := Fin.last M
  have hfirstLast : first ≠ last := by
    apply Fin.ne_of_val_ne
    simp [first, last, KWAdaptivePatchedData.lastMiddleIndex]
    have := patch.hM
    omega
  rw [fintype_prod_eq_two_factors G first last hfirstLast]
  · dsimp only [G, F, first, last]
    rw [show finProdFinEquiv (i, kwStairEvenLocal
          patch.lastMiddleIndex.castSucc) =
        kwStairEvenIndex i patch.lastMiddleIndex.castSucc by rfl,
      show finProdFinEquiv (i, kwStairOddLocal
          patch.lastMiddleIndex.castSucc) =
        kwStairOddIndex i patch.lastMiddleIndex.castSucc by rfl,
      show finProdFinEquiv (i, kwStairEvenLocal (Fin.last M)) =
        kwStairEvenIndex i (Fin.last M) by rfl,
      show finProdFinEquiv (i, kwStairOddLocal (Fin.last M)) =
        kwStairOddIndex i (Fin.last M) by rfl]
    have hlastMiddle : patch.lastMiddleIndex.succ = Fin.last M := by
      apply Fin.ext
      simp [KWAdaptivePatchedData.lastMiddleIndex]
      omega
    rw [kwStairEvenIndex_add_one, kwStairOddIndex_castSucc_add_one,
      hlastMiddle, kwStairEvenIndex_add_one, kwStairOddIndex_last_add_one]
    rw [patch.idealRawEdge_even_castSucc,
      patch.idealRawEdge_odd_castSucc,
      patch.idealRawEdge_even_last,
      patch.idealRawEdge_odd_last]
    have hzero : (0 : Fin (M + 1)) = (0 : Fin M).castSucc := by
      apply Fin.ext
      rfl
    rw [hzero, patch.idealRawEdge_even_castSucc,
      kwVectorTurnPhase_eq_one_of_eq rfl, one_mul]
    have hdelta : 0 < (1 / 2 : ℝ) *
        (patch.data.parameter i patch.lastMiddleIndex.succ.castSucc.succ -
          patch.data.parameter i patch.lastMiddleIndex.succ.castSucc.castSucc) :=
      mul_pos (by norm_num) (patch.middleDelta_pos i patch.lastMiddleIndex)
    have hi : i + 1 - 1 = i := by abel
    have hsourceScaled : kwComplexCross
        (-(patch.alpha (i + 1) * (-polygon.edgeVector i)))
        (patch.beta * polygon.edgeVector (i + 1)) ≠ 0 := by
      rw [show -(patch.alpha (i + 1) * (-polygon.edgeVector i)) =
          patch.alpha (i + 1) * polygon.edgeVector i by ring,
        kwComplexCross_mul_real_left,
        kwComplexCross_mul_real_right]
      exact mul_ne_zero (patch.halpha (i + 1)).ne'
        (mul_ne_zero patch.hbeta.ne' (hcross i))
    have haRe :
        (patch.alpha (i + 1) *
          (-polygon.edgeVector (i + 1 - 1))).re ≠ 0 := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.neg_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_ne_zero (patch.halpha (i + 1)).ne'
        (neg_ne_zero.mpr (hcoords (i + 1 - 1)).1)
    have haIm :
        (patch.alpha (i + 1) *
          (-polygon.edgeVector (i + 1 - 1))).im ≠ 0 := by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.neg_im,
        Complex.ofReal_im, zero_mul, add_zero]
      exact mul_ne_zero (patch.halpha (i + 1)).ne'
        (neg_ne_zero.mpr (hcoords (i + 1 - 1)).2)
    have hbRe :
        (patch.beta * polygon.edgeVector (i + 1)).re ≠ 0 := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      exact mul_ne_zero patch.hbeta.ne' (hcoords (i + 1)).1
    have hbIm :
        (patch.beta * polygon.edgeVector (i + 1)).im ≠ 0 := by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero]
      exact mul_ne_zero patch.hbeta.ne' (hcoords (i + 1)).2
    have hsourceScaled' : kwComplexCross
        (-(patch.alpha (i + 1) *
          (-polygon.edgeVector (i + 1 - 1))))
        (patch.beta * polygon.edgeVector (i + 1)) ≠ 0 := by
      simpa only [hi] using hsourceScaled
    have hcollapse := (patch.connector (i + 1)).phase_collapse
      haRe haIm hbRe hbIm hsourceScaled'
    have hcollapse' :
        kwVectorTurnPhase
              (-(patch.alpha (i + 1) * (-polygon.edgeVector i)))
              ((patch.connector (i + 1)).corner -
                patch.alpha (i + 1) * (-polygon.edgeVector i)) *
            kwVectorTurnPhase
              ((patch.connector (i + 1)).corner -
                patch.alpha (i + 1) * (-polygon.edgeVector i))
              (patch.beta * polygon.edgeVector (i + 1) -
                (patch.connector (i + 1)).corner) *
          kwVectorTurnPhase
            (patch.beta * polygon.edgeVector (i + 1) -
              (patch.connector (i + 1)).corner)
            (patch.beta * polygon.edgeVector (i + 1)) =
          kwVectorTurnPhase
            (-(patch.alpha (i + 1) * (-polygon.edgeVector i)))
            (patch.beta * polygon.edgeVector (i + 1)) := by
      simpa only [hi] using hcollapse
    have hedgeI := polygon.edgeVector_ne_zero i
    have hedgeNext := polygon.edgeVector_ne_zero (i + 1)
    have hfirstVector :
        (patch.connector (i + 1)).corner -
            patch.alpha (i + 1) * (-polygon.edgeVector i) ≠ 0 :=
      sub_ne_zero.mpr (by simpa only [hi] using
        (patch.connector (i + 1)).corner_ne_left)
    have hsecondVector :
        patch.beta * polygon.edgeVector (i + 1) -
            (patch.connector (i + 1)).corner ≠ 0 :=
      sub_ne_zero.mpr (patch.connector (i + 1)).corner_ne_right.symm
    have hleftScale := kwVectorTurnPhase_pos_left
      ((1 / 2 : ℝ) *
        (patch.data.parameter i patch.lastMiddleIndex.succ.castSucc.succ -
          patch.data.parameter i patch.lastMiddleIndex.succ.castSucc.castSucc))
      (patch.alpha (i + 1)) hdelta (patch.halpha (i + 1))
      (polygon.edgeVector i)
      ((patch.connector (i + 1)).corner -
        patch.alpha (i + 1) * (-polygon.edgeVector i)) hedgeI hfirstVector
    have hrightScale := kwVectorTurnPhase_pos_right
      ((1 / 2 : ℝ) *
        (patch.data.parameter (i + 1) (0 : Fin M).succ.castSucc.succ -
          patch.data.parameter (i + 1) (0 : Fin M).succ.castSucc.castSucc))
      patch.beta
      (mul_pos (by norm_num) (patch.middleDelta_pos (i + 1) 0))
      patch.hbeta
      (patch.beta * polygon.edgeVector (i + 1) -
        (patch.connector (i + 1)).corner)
      (polygon.edgeVector (i + 1)) hsecondVector hedgeNext
    have hsourceScale := kwVectorTurnPhase_pos_scales
      (patch.alpha (i + 1)) patch.beta
      (patch.halpha (i + 1)) patch.hbeta
      (polygon.edgeVector i) (polygon.edgeVector (i + 1))
      hedgeI hedgeNext
    have hleftScale' :
        kwVectorTurnPhase
            ((1 / 2 : ℝ) *
                (patch.data.parameter i
                    patch.lastMiddleIndex.succ.castSucc.succ -
                  patch.data.parameter i
                    patch.lastMiddleIndex.succ.castSucc.castSucc) *
              polygon.edgeVector i)
            ((patch.connector (i + 1)).corner -
              patch.alpha (i + 1) * (-polygon.edgeVector i)) =
          kwVectorTurnPhase
            (patch.alpha (i + 1) * polygon.edgeVector i)
            ((patch.connector (i + 1)).corner -
              patch.alpha (i + 1) * (-polygon.edgeVector i)) := by
      convert hleftScale using 1 <;> push_cast <;> ring
    have hrightScale' :
        kwVectorTurnPhase
            (patch.beta * polygon.edgeVector (i + 1) -
              (patch.connector (i + 1)).corner)
            ((1 / 2 : ℝ) *
                (patch.data.parameter (i + 1)
                    (0 : Fin M).succ.castSucc.succ -
                  patch.data.parameter (i + 1)
                    (0 : Fin M).succ.castSucc.castSucc) *
              polygon.edgeVector (i + 1)) =
          kwVectorTurnPhase
            (patch.beta * polygon.edgeVector (i + 1) -
              (patch.connector (i + 1)).corner)
            (patch.beta * polygon.edgeVector (i + 1)) := by
      convert hrightScale using 1 <;> push_cast <;> ring
    rw [hleftScale', hrightScale']
    rw [show -(patch.alpha (i + 1) * (-polygon.edgeVector i)) =
      patch.alpha (i + 1) * polygon.edgeVector i by ring] at hcollapse'
    rw [← mul_assoc, hcollapse', hsourceScale]
  · intro k hkFirst hkLast
    obtain ⟨q, rfl⟩ := Fin.eq_castSucc_of_ne_last hkLast
    have hq : q ≠ patch.lastMiddleIndex := by
      intro h
      apply hkFirst
      subst q
      rfl
    dsimp only [G, F]
    rw [show finProdFinEquiv (i, kwStairEvenLocal q.castSucc) =
        kwStairEvenIndex i q.castSucc by rfl,
      show finProdFinEquiv (i, kwStairOddLocal q.castSucc) =
        kwStairOddIndex i q.castSucc by rfl,
      kwStairEvenIndex_add_one, kwStairOddIndex_castSucc_add_one,
      patch.idealRawEdge_even_castSucc, patch.idealRawEdge_odd_castSucc]
    rw [kwVectorTurnPhase_eq_one_of_eq rfl, one_mul]
    have hqNext : q.val + 1 < M := by
      by_contra h
      apply hq
      apply Fin.ext
      simp [KWAdaptivePatchedData.lastMiddleIndex]
      omega
    let qnext : Fin M := ⟨q.val + 1, hqNext⟩
    have hidx : q.succ = qnext.castSucc := by apply Fin.ext; rfl
    rw [hidx, patch.idealRawEdge_even_castSucc]
    let d₁ : ℝ := (1 / 2) *
      (patch.data.parameter i qnext.castSucc.castSucc.succ -
        patch.data.parameter i qnext.castSucc.castSucc.castSucc)
    let d₂ : ℝ := (1 / 2) *
      (patch.data.parameter i qnext.succ.castSucc.succ -
        patch.data.parameter i qnext.succ.castSucc.castSucc)
    have hd₁raw := patch.middleDelta_pos i q
    rw [hidx] at hd₁raw
    have hd₁ : 0 < d₁ := mul_pos (by norm_num) hd₁raw
    have hd₂ : 0 < d₂ :=
      mul_pos (by norm_num) (patch.middleDelta_pos i qnext)
    have hphase := kwVectorTurnPhase_pos_scales d₁ d₂ hd₁ hd₂
      (polygon.edgeVector i) (polygon.edgeVector i)
      (polygon.edgeVector_ne_zero i) (polygon.edgeVector_ne_zero i)
    have hphase' :
        kwVectorTurnPhase
            ((1 / 2 : ℝ) *
                (patch.data.parameter i qnext.castSucc.castSucc.succ -
                  patch.data.parameter i qnext.castSucc.castSucc.castSucc) *
              polygon.edgeVector i)
            ((1 / 2 : ℝ) *
                (patch.data.parameter i qnext.succ.castSucc.succ -
                  patch.data.parameter i qnext.succ.castSucc.castSucc) *
              polygon.edgeVector i) =
          kwVectorTurnPhase (polygon.edgeVector i) (polygon.edgeVector i) := by
      convert hphase using 1 <;> dsimp only [d₁, d₂] <;> push_cast <;> ring
    rw [hphase']
    exact kwVectorTurnPhase_eq_one_of_eq rfl


theorem KWAdaptivePatchedData.ideal_phaseCycle_eq_source
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (hcross : ∀ i : Fin n, kwComplexCross (polygon.edgeVector i)
      (polygon.edgeVector (i + 1)) ≠ 0) :
    kwVectorPhaseCycle (List.ofFn (kwRawEdge patch.idealVertex)) =
      kwVectorPhaseCycle polygon.edgeList := by
  rw [kwVectorPhaseCycle_ofFn, KWFiniteSimplePolygon.edgeList,
    kwVectorPhaseCycle_ofFn]
  unfold kwLoopPhaseProduct
  let e := finProdFinEquiv (m := n) (n := 2 * (M + 1))
  calc
    (∏ j : Fin (n * (2 * (M + 1))),
        kwVectorTurnPhase (kwRawEdge patch.idealVertex j)
          (kwRawEdge patch.idealVertex (j + 1))) =
        ∏ p : Fin n × Fin (2 * (M + 1)),
          kwVectorTurnPhase (kwRawEdge patch.idealVertex (e p))
            (kwRawEdge patch.idealVertex (e p + 1)) := by
      exact (Fintype.prod_equiv e _ _ fun _ ↦ rfl).symm
    _ = ∏ i : Fin n, kwVectorTurnPhase (polygon.edgeVector i)
          (polygon.edgeVector (i + 1)) := by
      rw [Fintype.prod_prod_type]
      apply Fintype.prod_congr
      intro i
      exact patch.ideal_block_phase hcoords hcross i

end StatMech.FrontierA
