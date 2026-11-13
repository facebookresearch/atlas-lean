/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Convex.Basic
import MathlibExt.Analysis.Convex.KKM
import MathlibExt.Analysis.InnerProductSpace.ConvexProjection
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Brouwer's fixed-point theorem

A continuous map from a nonempty compact convex subset `K` of a finite-dimensional real normed
space into itself has a fixed point in `K`.

The proof derives the theorem from the closed Knaster–Kuratowski–Mazurkiewicz lemma
`MathlibExt.Analysis.Convex.KKM.kkm_lemma`. On the standard simplex, the closed sets
`F i = {x | (f x).weights i ≤ x.weights i}` cover the simplex in the KKM sense, and a common
point is a fixed point. A general `K` is transported to Euclidean space, placed inside a large
simplex, and retracted onto by the nearest-point projection. The `_of_kkm` theorems take the KKM
statement as the hypothesis `KKMProperty`; `kkmProperty` discharges it.

## Main results

* `exists_fixedPoint_stdSimplex`: Brouwer's theorem on the standard simplex.
* `exists_fixedPoint`: Brouwer's theorem for a nonempty compact convex `K`.

## References

* B. Knaster, C. Kuratowski, S. Mazurkiewicz, *Ein Beweis des Fixpunktsatzes für
  n-dimensionale Simplexe*, Fundamenta Mathematicae 14 (1929), 132–137.
* L. E. J. Brouwer, *Über Abbildung von Mannigfaltigkeiten*, Math. Ann. 71 (1911), 97–115.
* A. Mas-Colell, M. D. Whinston, J. R. Green, *Microeconomic Theory*, Oxford University Press
  (1995), Mathematical Appendix, Theorem M.I.1.
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.BrouwerFixedPoint

/-- The closed Knaster–Kuratowski–Mazurkiewicz property of every standard simplex: if closed sets
`F i` indexed by the vertices cover the simplex so that each point `x` lies in some `F i` with
`x.weights i > 0`, then the sets have a common point. In Atlas this is exactly the statement of
`MathlibExt.Analysis.Convex.KKM.kkm_lemma`, quantified over the dimension `n`. -/
def KKMProperty : Prop :=
  ∀ (n : ℕ) (F : Fin (n + 1) → Set (Convexity.StdSimplex ℝ (Fin (n + 1)))),
    (∀ i, IsClosed (F i)) →
    (∀ x : Convexity.StdSimplex ℝ (Fin (n + 1)), ∃ i : Fin (n + 1), 0 < x.weights i ∧ x ∈ F i) →
    ∃ x : Convexity.StdSimplex ℝ (Fin (n + 1)), ∀ i, x ∈ F i

/-- Brouwer's fixed-point theorem on the standard simplex, derived from the KKM property:
every continuous self-map of the `(n+1)`-vertex standard simplex has a fixed point. -/
theorem exists_fixedPoint_stdSimplex_of_kkm (hKKM : KKMProperty) {n : ℕ}
    (f : Convexity.StdSimplex ℝ (Fin (n + 1)) → Convexity.StdSimplex ℝ (Fin (n + 1)))
    (hf : Continuous f) :
    ∃ x : Convexity.StdSimplex ℝ (Fin (n + 1)), f x = x := by
  classical
  have hclosed : ∀ i : Fin (n + 1),
      IsClosed {x : Convexity.StdSimplex ℝ (Fin (n + 1)) | (f x).weights i ≤ x.weights i} := by
    intro i
    have h1 : Continuous
        (fun x : Convexity.StdSimplex ℝ (Fin (n + 1)) => (f x).weights i) :=
      (Convexity.StdSimplex.continuous_weights_apply ℝ i).comp hf
    have h2 : Continuous
        (fun x : Convexity.StdSimplex ℝ (Fin (n + 1)) => x.weights i) :=
      Convexity.StdSimplex.continuous_weights_apply ℝ i
    exact isClosed_le h1 h2
  have hcover : ∀ x : Convexity.StdSimplex ℝ (Fin (n + 1)),
      ∃ i : Fin (n + 1), 0 < x.weights i ∧
        x ∈ {x : Convexity.StdSimplex ℝ (Fin (n + 1)) |
          (f x).weights i ≤ x.weights i} := by
    intro x
    by_contra hcon
    have hcon' : ∀ i : Fin (n + 1),
        0 < x.weights i → ¬ (f x).weights i ≤ x.weights i := by
      intro i hi
      exact (not_and.mp (not_exists.mp hcon i)) hi
    have hle : ∀ i : Fin (n + 1), x.weights i ≤ (f x).weights i := by
      intro i
      by_cases hi : 0 < x.weights i
      · exact le_of_lt (lt_of_not_ge (hcon' i hi))
      · have h0 : x.weights i = 0 :=
          le_antisymm (le_of_not_gt hi) (Convexity.StdSimplex.weights_nonneg i)
        rw [h0]
        exact Convexity.StdSimplex.weights_nonneg i
    have hpos : ∃ i : Fin (n + 1), 0 < x.weights i := by
      by_contra hall
      have hall' : ∀ i : Fin (n + 1), x.weights i ≤ 0 := fun i => le_of_not_gt
        (not_exists.mp hall i)
      have hsum0 : ∑ i : Fin (n + 1), x.weights i = 0 :=
        Finset.sum_eq_zero fun i _ =>
          le_antisymm (hall' i) (Convexity.StdSimplex.weights_nonneg i)
      have hsum1 : ∑ i : Fin (n + 1), x.weights i = 1 := x.total_of_fintype
      rw [hsum0] at hsum1
      norm_num at hsum1
    obtain ⟨i0, hi0⟩ := hpos
    have hlt : ∑ i : Fin (n + 1), x.weights i
        < ∑ i : Fin (n + 1), (f x).weights i :=
      Finset.sum_lt_sum (s := Finset.univ) (fun i _ => hle i)
        ⟨i0, Finset.mem_univ i0, lt_of_not_ge (hcon' i0 hi0)⟩
    rw [x.total_of_fintype, (f x).total_of_fintype] at hlt
    exact lt_irrefl 1 hlt
  obtain ⟨x, hx⟩ := hKKM n _ hclosed hcover
  have hsum : ∑ i : Fin (n + 1), (f x).weights i
      = ∑ i : Fin (n + 1), x.weights i := by
    rw [(f x).total_of_fintype, x.total_of_fintype]
  have heq : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))),
      (f x).weights i = x.weights i :=
    (Finset.sum_eq_sum_iff_of_le (fun i _ => hx i)).mp hsum
  refine ⟨x, Convexity.StdSimplex.ext ?_⟩
  exact Finsupp.ext fun i => heq i (Finset.mem_univ i)

/-- Vertices of a large simplex in `EuclideanSpace ℝ (Fin d)`: vertex `0` is the constant
`-c` vector; vertex `k.succ` is `-c` except for `d * c` in coordinate `k`. -/
private noncomputable def brouwerVertices (d : ℕ) (c : ℝ) :
    Fin (d + 1) → EuclideanSpace ℝ (Fin d) :=
  Fin.cons (WithLp.toLp 2 (fun _ => -c))
    (fun k => WithLp.toLp 2 (fun j => if j = k then (d : ℝ) * c else -c))

private theorem brouwerVertices_add (d : ℕ) (c : ℝ) (i : Fin (d + 1)) (j : Fin d) :
    (brouwerVertices d c i).ofLp j + c
      = if i = j.succ then ((d : ℝ) + 1) * c else 0 := by
  refine Fin.cases ?hz ?hs i
  · unfold brouwerVertices
    rw [Fin.cons_zero, PiLp.toLp_apply]
    rw [ite_eq_right (fun h => Fin.succ_ne_zero j h.symm)]
    simp
  · intro k
    unfold brouwerVertices
    rw [Fin.cons_succ, PiLp.toLp_apply]
    by_cases h : j = k
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl]
      ring
    · rw [ite_eq_right h]
      have h2 : ¬ k.succ = j.succ := fun hh => h (Fin.succ_inj.mp hh).symm
      rw [ite_eq_right h2]
      simp

/-- The affine map from the standard simplex onto the large simplex with vertices
`brouwerVertices d c`. -/
private noncomputable def brouwerPhi (d : ℕ) (c : ℝ) :
    Convexity.StdSimplex ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin d) :=
  fun x => WithLp.toLp 2 (fun j => ∑ i, x.weights i * (brouwerVertices d c i).ofLp j)

private theorem brouwerPhi_apply (d : ℕ) (c : ℝ)
    (x : Convexity.StdSimplex ℝ (Fin (d + 1))) (j : Fin d) :
    (brouwerPhi d c x).ofLp j
      = ∑ i, x.weights i * (brouwerVertices d c i).ofLp j := rfl

private theorem brouwerPhi_continuous (d : ℕ) (c : ℝ) :
    Continuous (brouwerPhi d c) := by
  have hψ : Continuous (fun x : Convexity.StdSimplex ℝ (Fin (d + 1)) =>
      (fun j : Fin d => ∑ i, x.weights i * (brouwerVertices d c i).ofLp j)) := by
    rw [continuous_pi_iff]
    intro j
    refine continuous_finsetSum _ fun i _ => ?_
    exact (Convexity.StdSimplex.continuous_weights_apply ℝ i).mul continuous_const
  have hcomp := (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp hψ
  exact hcomp

/-- Key computation: the `j`-th coordinate of `brouwerPhi` determines the `j.succ` weight. -/
private theorem brouwerPhi_key (d : ℕ) (c : ℝ) (w : Fin (d + 1) → ℝ) (j : Fin d) :
    (∑ i, w i * (brouwerVertices d c i).ofLp j) + c * (∑ i, w i)
      = w j.succ * (((d : ℝ) + 1) * c) := by
  have h1 : (∑ i, w i * (brouwerVertices d c i).ofLp j) + c * (∑ i, w i)
      = ∑ i, w i * ((brouwerVertices d c i).ofLp j + c) := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h1]
  simp only [brouwerVertices_add, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ j.succ (fun i => w i * (((d : ℝ) + 1) * c))]
  rw [ite_eq_left (Finset.mem_univ _)]

private theorem brouwerPhi_injective (d : ℕ) (c : ℝ) (hc : 0 < c) :
    Function.Injective (brouwerPhi d c) := by
  intro x y hxy
  have hd1 : (0:ℝ) < (d:ℝ) + 1 := by
    have h : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    linarith
  have hD : ((d : ℝ) + 1) * c ≠ 0 := ne_of_gt (mul_pos hd1 hc)
  have hwsucc : ∀ j : Fin d, x.weights j.succ = y.weights j.succ := by
    intro j
    have hj : (brouwerPhi d c x).ofLp j = (brouwerPhi d c y).ofLp j :=
      congrArg (fun z => z.ofLp j) hxy
    rw [brouwerPhi_apply, brouwerPhi_apply] at hj
    have kx := brouwerPhi_key d c x.weights j
    have ky := brouwerPhi_key d c y.weights j
    rw [x.total_of_fintype] at kx
    rw [y.total_of_fintype] at ky
    have hDD : x.weights j.succ * (((d:ℝ) + 1) * c)
        = y.weights j.succ * (((d:ℝ) + 1) * c) := by
      rw [← kx, ← ky, hj]
    exact mul_right_cancel₀ hD hDD
  have h0 : x.weights 0 = y.weights 0 := by
    have hx := x.total_of_fintype
    have hy := y.total_of_fintype
    rw [Fin.sum_univ_succ] at hx hy
    have hss : (∑ i : Fin d, x.weights i.succ)
        = ∑ i : Fin d, y.weights i.succ :=
      Finset.sum_congr rfl fun j _ => hwsucc j
    rw [hss] at hx
    linarith
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  refine Fin.cases ?_ ?_ i
  · exact h0
  · intro j
    exact hwsucc j

/-- Every point of the closed ball of radius `M` lies in the range of `brouwerPhi`, via
explicit barycentric coordinates. -/
private theorem brouwerPhi_mem_range (d : ℕ) (c M : ℝ) (hc : 0 < c) (hM0 : 0 ≤ M)
    (hcM : M ≤ c) (hcdM : (d : ℝ) * M ≤ c) (y : EuclideanSpace ℝ (Fin d))
    (hy : y ∈ Metric.closedBall 0 M) : y ∈ Set.range (brouwerPhi d c) := by
  classical
  have hd1 : (0:ℝ) < (d:ℝ) + 1 := by
    have h : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    linarith
  have hDpos : (0:ℝ) < ((d:ℝ) + 1) * c := mul_pos hd1 hc
  have hDne : ((d:ℝ) + 1) * c ≠ 0 := ne_of_gt hDpos
  have hynorm : ‖y‖ ≤ M := by
    have h := (Metric.mem_closedBall.mp hy : dist y 0 ≤ M)
    rwa [dist_zero_right] at h
  have hsq : ‖y‖ ^ 2 ≤ M ^ 2 :=
    sq_le_sq' (le_trans (neg_nonpos.mpr hM0) (norm_nonneg y)) hynorm
  have h5 : ∀ j : Fin d, |y.ofLp j| ≤ M := by
    intro j
    apply abs_le_of_sq_le_sq _ hM0
    calc (y.ofLp j) ^ 2 ≤ ∑ k, (y.ofLp k) ^ 2 :=
            Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ j)
        _ = ‖y‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq y).symm
        _ ≤ M ^ 2 := hsq
  have hsum_le : ∑ j : Fin d, y.ofLp j ≤ c := by
    calc ∑ j : Fin d, y.ofLp j ≤ ∑ j : Fin d, |y.ofLp j| :=
            Finset.sum_le_sum fun j _ => le_abs_self _
        _ ≤ ∑ j : Fin d, M := Finset.sum_le_sum fun j _ => h5 j
        _ = (d:ℝ) * M := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ c := hcdM
  set w : Fin (d + 1) → ℝ :=
    Fin.cons (1 - ∑ j : Fin d, (y.ofLp j + c) / (((d:ℝ) + 1) * c))
      (fun k => (y.ofLp k + c) / (((d:ℝ) + 1) * c)) with hw
  have hw0 : w 0 = 1 - ∑ j : Fin d, (y.ofLp j + c) / (((d:ℝ) + 1) * c) := by
    rw [hw, Fin.cons_zero]
  have hws : ∀ k : Fin d, w k.succ = (y.ofLp k + c) / (((d:ℝ) + 1) * c) := by
    intro k
    rw [hw, Fin.cons_succ]
  have hsumw : (∑ j : Fin d, (y.ofLp j + c) / (((d:ℝ) + 1) * c))
      = (∑ j : Fin d, y.ofLp j + (d:ℝ) * c) / (((d:ℝ) + 1) * c) := by
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hw0_nonneg : 0 ≤ w 0 := by
    rw [hw0, hsumw, sub_nonneg, div_le_one hDpos]
    have hexp : ((d:ℝ) + 1) * c = (d:ℝ) * c + c := by ring
    rw [hexp]
    linarith [hsum_le]
  have hw_nonneg : ∀ i : Fin (d + 1), 0 ≤ w i := by
    intro i
    refine Fin.cases ?_ ?_ i
    · exact hw0_nonneg
    · intro k
      rw [hws k]
      apply div_nonneg _ (le_of_lt hDpos)
      have hle := (abs_le.mp (h5 k)).1
      linarith [hcM]
  have hwsum : ∑ i : Fin (d + 1), w i = 1 := by
    rw [Fin.sum_univ_succ, hw0]
    simp only [hws]
    ring
  set x : Convexity.StdSimplex ℝ (Fin (d + 1)) :=
    { weights := Finsupp.equivFunOnFinite.symm w
      nonneg m := by simpa using hw_nonneg m
      total := by simpa [Finsupp.sum_fintype] using hwsum } with hx
  have hwx : ∀ i : Fin (d + 1), x.weights i = w i := fun i => by simp [hx]
  refine ⟨x, ?_⟩
  apply PiLp.ext
  intro j
  rw [brouwerPhi_apply]
  simp only [hwx]
  have hkey := brouwerPhi_key d c w j
  rw [hwsum] at hkey
  rw [hws j] at hkey
  have hdiv : (y.ofLp j + c) / (((d:ℝ) + 1) * c) * (((d:ℝ) + 1) * c)
      = y.ofLp j + c :=
    div_mul_cancel₀ _ hDne
  rw [hdiv] at hkey
  linarith [hkey]

open MathlibExt.Analysis.InnerProductSpace.ConvexProjection in
/-- Brouwer's fixed-point theorem, derived from the KKM property: a continuous map from a
nonempty compact convex subset `K` of a finite-dimensional real normed space into itself has a
fixed point in `K`. -/
theorem exists_fixedPoint_of_kkm (hKKM : KKMProperty) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {K : Set E} (hKc : IsCompact K)
    (hKcv : Convex ℝ K) (hKne : K.Nonempty) {f : E → E} (hf : ContinuousOn f K)
    (hfK : Set.MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  classical
  set d := Module.finrank ℝ E with hd
  have hfin : Module.finrank ℝ E = Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) := by
    rw [finrank_euclideanSpace_fin, ← hd]
  set e : E ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
    ContinuousLinearEquiv.ofFinrankEq hfin with he
  set K' : Set (EuclideanSpace ℝ (Fin d)) := e '' K with hK'
  have hK'c : IsCompact K' := hKc.image e.continuous
  have hK'cv : Convex ℝ K' := hKcv.linear_image (e.toLinearEquiv.toLinearMap)
  obtain ⟨x0, hx0⟩ := hKne
  have hK'ne : K'.Nonempty := by
    rw [hK']
    exact ⟨e x0, x0, hx0, rfl⟩
  have hK'complete : IsComplete K' := hK'c.isClosed.isComplete
  set f' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun y => e (f (e.symm y)) with hf'
  have hmaps1 : Set.MapsTo (fun y => e.symm y) K' K := by
    intro y hy
    rw [hK'] at hy
    obtain ⟨x, hxK, rfl⟩ := hy
    change e.symm (e x) ∈ K
    rw [e.symm_apply_apply]
    exact hxK
  have hf'K : Set.MapsTo f' K' K' := by
    intro y hy
    rw [hK'] at hy
    obtain ⟨x, hxK, rfl⟩ := hy
    change e (f (e.symm (e x))) ∈ e '' K
    rw [e.symm_apply_apply]
    exact ⟨f x, hfK hxK, rfl⟩
  have hf'cont : ContinuousOn f' K' := by
    have hcomp1 : ContinuousOn (f ∘ fun y => e.symm y) K' :=
      hf.comp e.symm.continuous.continuousOn hmaps1
    have hmaps2 : Set.MapsTo (f ∘ fun y => e.symm y) K' K := hfK.comp hmaps1
    have hcomp2 : ContinuousOn (⇑e ∘ (f ∘ fun y => e.symm y)) K' :=
      e.continuous.continuousOn.comp hcomp1 hmaps2
    exact hcomp2
  obtain ⟨r, hr⟩ := hK'c.isBounded.subset_closedBall 0
  set M : ℝ := |r| + 1 with hM
  have hM0 : 0 ≤ M := add_nonneg (abs_nonneg r) zero_le_one
  have hMsub : K' ⊆ Metric.closedBall 0 M := by
    refine hr.trans ?_
    apply Metric.closedBall_subset_closedBall
    calc r ≤ |r| := le_abs_self r
      _ ≤ |r| + 1 := le_add_of_nonneg_right zero_le_one
  set c : ℝ := ((d : ℝ) + 1) * M + 1 with hc
  have hd1' : (0:ℝ) ≤ (d:ℝ) + 1 := add_nonneg (Nat.cast_nonneg d) zero_le_one
  have hc0 : 0 < c := by
    have h : (0:ℝ) ≤ ((d:ℝ) + 1) * M := mul_nonneg hd1' hM0
    rw [hc]
    linarith [h]
  have hexp : ((d:ℝ) + 1) * M = (d:ℝ) * M + M := by ring
  have hdM0 : (0:ℝ) ≤ (d:ℝ) * M := mul_nonneg (Nat.cast_nonneg d) hM0
  have hcM : M ≤ c := by rw [hc]; linarith [hexp, hdM0]
  have hcdM : (d:ℝ) * M ≤ c := by rw [hc]; linarith [hexp, hM0]
  have hK'sub_range : K' ⊆ Set.range (brouwerPhi d c) := by
    intro y hy
    exact brouwerPhi_mem_range d c M hc0 hM0 hcM hcdM y (hMsub hy)
  have hinj : Function.Injective (brouwerPhi d c) := brouwerPhi_injective d c hc0
  have hφcont : Continuous (brouwerPhi d c) := brouwerPhi_continuous d c
  set ψ : Convexity.StdSimplex ℝ (Fin (d + 1)) ≃ₜ ↥(Set.range (brouwerPhi d c)) :=
    Continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofInjective (brouwerPhi d c) hinj)
      (Continuous.subtype_mk hφcont (fun x => Set.mem_range_self x)) with hψ
  set P := convexProjection K' with hP
  have hPcont : Continuous P := (lipschitzWith_convexProjection hK'ne hK'complete hK'cv).continuous
  have hmem : ∀ x : Convexity.StdSimplex ℝ (Fin (d + 1)),
      P (f' (P (Subtype.val (ψ x)))) ∈ Set.range (brouwerPhi d c) := by
    intro x
    exact hK'sub_range (convexProjection_mem hK'ne hK'complete hK'cv _)
  set g' : Convexity.StdSimplex ℝ (Fin (d + 1))
      → Convexity.StdSimplex ℝ (Fin (d + 1)) :=
    fun x => ψ.symm ⟨P (f' (P (Subtype.val (ψ x)))), hmem x⟩ with hg'
  have hs1 : Continuous (fun x : Convexity.StdSimplex ℝ (Fin (d + 1)) =>
      Subtype.val (ψ x : ↥(Set.range (brouwerPhi d c)))) :=
    continuous_subtype_val.comp ψ.continuous
  have hg'cont : Continuous g' := by
    have h1 : ContinuousOn (fun x : Convexity.StdSimplex ℝ (Fin (d + 1)) =>
        P (Subtype.val (ψ x))) Set.univ :=
      hPcont.continuousOn.comp hs1.continuousOn (fun x _ => Set.mem_univ _)
    have hm1 : Set.MapsTo (fun x : Convexity.StdSimplex ℝ (Fin (d + 1)) =>
        P (Subtype.val (ψ x))) Set.univ K' := by
      intro x _
      exact convexProjection_mem hK'ne hK'complete hK'cv _
    have h2 : ContinuousOn (fun x : Convexity.StdSimplex ℝ (Fin (d + 1)) =>
        f' (P (Subtype.val (ψ x)))) Set.univ :=
      hf'cont.comp h1 hm1
    have hm2 : Set.MapsTo (fun x : Convexity.StdSimplex ℝ (Fin (d + 1)) =>
        f' (P (Subtype.val (ψ x)))) Set.univ K' :=
      hf'K.comp hm1
    have h3 : ContinuousOn (fun x : Convexity.StdSimplex ℝ (Fin (d + 1)) =>
        P (f' (P (Subtype.val (ψ x))))) Set.univ :=
      hPcont.continuousOn.comp h2 (fun x _ => Set.mem_univ _)
    have h3c : Continuous (fun x : Convexity.StdSimplex ℝ (Fin (d + 1)) =>
        P (f' (P (Subtype.val (ψ x))))) :=
      continuousOn_univ.mp h3
    have h4 : Continuous (fun x : Convexity.StdSimplex ℝ (Fin (d + 1)) =>
        (⟨P (f' (P (Subtype.val (ψ x)))), hmem x⟩ :
          ↥(Set.range (brouwerPhi d c)))) :=
      Continuous.subtype_mk h3c hmem
    exact ψ.continuous_symm.comp h4
  obtain ⟨x₀, hx₀⟩ := exists_fixedPoint_stdSimplex_of_kkm hKKM g' hg'cont
  have hfix : P (f' (P (Subtype.val (ψ x₀)))) = Subtype.val (ψ x₀) := by
    have h1 : ψ (g' x₀) = ψ x₀ := congrArg (fun z => ψ z) hx₀
    have h2 : ψ (g' x₀)
        = (⟨P (f' (P (Subtype.val (ψ x₀)))), hmem x₀⟩ :
          ↥(Set.range (brouwerPhi d c))) :=
      ψ.toEquiv.apply_symm_apply _
    rw [h2] at h1
    exact congrArg Subtype.val h1
  have hPmem : P (Subtype.val (ψ x₀)) ∈ K' :=
    convexProjection_mem hK'ne hK'complete hK'cv _
  have hf'mem : f' (P (Subtype.val (ψ x₀))) ∈ K' := hf'K hPmem
  have hProj : P (f' (P (Subtype.val (ψ x₀)))) = f' (P (Subtype.val (ψ x₀))) :=
    convexProjection_eq_self_of_mem hK'ne hK'complete hK'cv hf'mem
  rw [hProj] at hfix
  have hzK : Subtype.val (ψ x₀) ∈ K' := by
    rw [← hfix]
    exact hf'mem
  have hPz : P (Subtype.val (ψ x₀)) = Subtype.val (ψ x₀) :=
    convexProjection_eq_self_of_mem hK'ne hK'complete hK'cv hzK
  rw [hPz] at hfix
  obtain ⟨x, hxK, hzx⟩ := hzK
  refine ⟨x, hxK, ?_⟩
  have hsym : e.symm (Subtype.val (ψ x₀)) = x := by
    rw [← hzx]
    exact e.symm_apply_apply x
  have hfz2 : e (f (e.symm (Subtype.val (ψ x₀)))) = Subtype.val (ψ x₀) := hfix
  rw [hsym, ← hzx] at hfz2
  have hcon : e.symm (e (f x)) = e.symm (e x) := congrArg (fun w => e.symm w) hfz2
  rw [e.symm_apply_apply, e.symm_apply_apply] at hcon
  exact hcon

end MathlibExt.Analysis.Convex.BrouwerFixedPoint

namespace MathlibExt.Analysis.Convex.BrouwerFixedPoint

/-- The KKM property of every standard simplex, from Atlas's `kkm_lemma`. -/
theorem kkmProperty : KKMProperty :=
  fun n => MathlibExt.Analysis.Convex.KKM.kkm_lemma (n := n)

/-- Brouwer's fixed-point theorem on the standard simplex. -/
theorem exists_fixedPoint_stdSimplex {n : ℕ}
    (f : Convexity.StdSimplex ℝ (Fin (n + 1)) → Convexity.StdSimplex ℝ (Fin (n + 1)))
    (hf : Continuous f) :
    ∃ x : Convexity.StdSimplex ℝ (Fin (n + 1)), f x = x :=
  exists_fixedPoint_stdSimplex_of_kkm kkmProperty f hf

/-- Brouwer's fixed-point theorem for a nonempty compact convex set. -/
theorem exists_fixedPoint {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {K : Set E} (hKc : IsCompact K)
    (hKcv : Convex ℝ K) (hKne : K.Nonempty) {f : E → E} (hf : ContinuousOn f K)
    (hfK : Set.MapsTo f K K) :
    ∃ x ∈ K, f x = x :=
  exists_fixedPoint_of_kkm kkmProperty hKc hKcv hKne hf hfK

end MathlibExt.Analysis.Convex.BrouwerFixedPoint
