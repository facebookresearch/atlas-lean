/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.LovaszThetaBody
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# The Lovász number as a supremum over the theta body

For a finite graph, the Lovász number equals the supremum of the coordinate sum on its theta
body. The reverse inequality uses convex separation of the vectors dominated by labeling costs.
-/

public section

namespace MathlibExt.Combinatorics.SimpleGraph.LovaszThetaBodyWanted

open MathlibExt.Combinatorics.SimpleGraph.LovaszTheta

section

open scoped RealInnerProductSpace

variable {V : Type*} {G : SimpleGraph V}

/-- Vectors dominated by the costs of a labeling. We use a unit handle and project it onto
each label line, so that the cost at a vertex is both the squared norm and the handle component
of the projected label. In these coordinates, direct sums realize convex combinations. -/
private def costMinorants (G : SimpleGraph V) : Set (V → ℝ) :=
  {x | ∃ (d : ℕ) (a : V → EuclideanSpace ℝ (Fin d)) (c : EuclideanSpace ℝ (Fin d)),
    ⟪c, c⟫ = 1 ∧ IsOrthogonalLabeling G a ∧
    (∀ v, ⟪a v, a v⟫ = ⟪c, a v⟫) ∧ ∀ v, x v ≤ ⟪c, a v⟫}

private theorem mem_costMinorants_of_nonpos {x : V → ℝ} (hx : x ≤ 0) :
    x ∈ costMinorants G := by
  refine ⟨1, fun _ => 0, EuclideanSpace.single 0 1, by simp, ?_, by simp, ?_⟩
  · intro u v _ _
    simp
  · intro v
    simpa using hx v

private theorem cost_mem_costMinorants {d : ℕ} {a : V → EuclideanSpace ℝ (Fin d)}
    (ha : IsOrthogonalLabeling G a) (c : EuclideanSpace ℝ (Fin d)) :
    (fun v => cost c (a v)) ∈ costMinorants G := by
  by_cases hc : c = 0
  · subst c
    apply mem_costMinorants_of_nonpos
    intro v
    simp [cost]
  let h := NormedSpace.normalize c
  let u := fun v => NormedSpace.normalize (a v)
  let b := fun v => ⟪h, u v⟫ • u v
  refine ⟨d, b, h, by simp [h, NormedSpace.norm_normalize hc],
    ?_, ?_, ?_⟩
  · intro i j hij hn
    simp [b, u, NormedSpace.normalize, real_inner_smul_left, real_inner_smul_right, ha hij hn]
  · intro v
    by_cases hv : a v = 0
    · simp [b, u, hv]
    · rw [show b v = ⟪h, u v⟫ • u v from rfl, real_inner_smul_left]
      simp only [real_inner_smul_right, real_inner_self_eq_norm_sq,
        show ‖u v‖ = 1 from NormedSpace.norm_normalize hv, one_pow, mul_one]
  · intro v
    apply le_of_eq
    simp [b, u, h, cost, NormedSpace.normalize, real_inner_smul_left, real_inner_smul_right,
      div_eq_mul_inv]
    ring

private theorem convex_costMinorants (G : SimpleGraph V) : Convex ℝ (costMinorants G) := by
  rintro x ⟨d, a, c, hc, ha, hca, hx⟩ y ⟨e, b, k, hk, hb, hkb, hy⟩ s t hs ht hst
  let E := WithLp 2 (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e))
  let mix (u : EuclideanSpace ℝ (Fin d)) (v : EuclideanSpace ℝ (Fin e)) : E :=
    WithLp.toLp 2 (Real.sqrt s • u, Real.sqrt t • v)
  have inner_mix u v u' v' : ⟪mix u v, mix u' v'⟫ = s * ⟪u, u'⟫ + t * ⟪v, v'⟫ := by
    change ⟪√s • u, √s • u'⟫ + ⟪√t • v, √t • v'⟫ = _
    simp only [real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
      Real.mul_self_sqrt hs, Real.mul_self_sqrt ht]
  let iso := (stdOrthonormalBasis ℝ E).repr
  refine ⟨_, fun v => iso (mix (a v) (b v)), iso (mix c k), ?_, ?_, ?_, ?_⟩
  · simpa only [LinearIsometryEquiv.inner_map_map, inner_mix, hc, hk, mul_one] using hst
  · intro i j hij hn
    simp [LinearIsometryEquiv.inner_map_map, inner_mix, ha hij hn, hb hij hn]
  · intro v
    simp only [LinearIsometryEquiv.inner_map_map, inner_mix, hca, hkb]
  · intro v
    rw [LinearIsometryEquiv.inner_map_map, inner_mix]
    exact add_le_add (mul_le_mul_of_nonneg_left (hx v) hs) (mul_le_mul_of_nonneg_left (hy v) ht)

private theorem const_notMem_costMinorants {t : ℝ} (ht : 0 < t) (hlt : t < lovaszTheta G) :
    (fun _ : V => 1 / t) ∉ costMinorants G := by
  rintro ⟨d, a, c, hc, ha, hca, hx⟩
  apply hlt.not_ge
  apply csInf_le (s := thetaFeasible G) ⟨0, fun _ h => h.1⟩
  refine ⟨ht.le, d, a, c, ?_, ha, fun v => ?_⟩
  · rintro rfl
    simp at hc
  · have hcost : cost c (a v) = ⟪c, a v⟫ := by
      rw [cost, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hc, one_mul, hca]
      simp [sq]
    rw [hcost, mul_comm]
    exact (div_le_iff₀ ht).mp (hx v)

private theorem interior_costMinorants_nonempty [Finite V] (G : SimpleGraph V) :
    (interior (costMinorants G)).Nonempty := by
  let U : Set (V → ℝ) := ⋂ v, {x | x v < 0}
  have hopen : IsOpen U :=
    isOpen_iInter_of_finite fun v => isOpen_lt (continuous_apply v) continuous_const
  have hsub : U ⊆ costMinorants G := fun _ hx =>
    mem_costMinorants_of_nonpos fun v => (Set.mem_iInter.mp hx v).le
  refine ⟨fun _ => -1, interior_maximal hsub hopen (Set.mem_iInter.mpr fun _ => ?_)⟩
  exact (neg_one_lt_zero : (-1 : ℝ) < 0)

variable [Fintype V]

/-- Separating the constant vector of height `1 / t` from the cost minorants gives a
nonnegative linear functional. Its coefficients, suitably scaled, form a point of the theta
body of coordinate sum `t`. -/
private theorem exists_mem_th_sum_eq {t : ℝ} (ht : 0 < t) (hlt : t < lovaszTheta G) :
    ∃ x ∈ th G, ∑ v, x v = t := by
  classical
  let q : V → ℝ := fun _ => 1 / t
  obtain ⟨f, hf, hsep⟩ := geometric_hahn_banach_of_nonempty_interior_point
    (convex_costMinorants G) (x := q)
    (fun h => const_notMem_costMinorants ht hlt (interior_subset h))
    (interior_costMinorants_nonempty G)
  let w (v : V) : ℝ := f (Pi.single v 1)
  have eval (z : V → ℝ) : f z = ∑ v, z v * w v := by
    calc
      f z = f (∑ v, Pi.single v (z v)) := by rw [Finset.univ_sum_single]
      _ = ∑ v, z v * w v := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← mul_one (z v), ← smul_eq_mul, Pi.single_smul', map_smul]
        simp [w]
  have hw (v : V) : 0 ≤ w v := by
    by_contra! h
    obtain ⟨r, hr, hrq⟩ := exists_pos_lt_mul (neg_pos.mpr h) (f q)
    have hneg : (-r) • (Pi.single v 1 : V → ℝ) ≤ 0 := by
      intro j
      by_cases hj : j = v <;> simp [hj, hr.le]
    have hh := hsep _ (mem_costMinorants_of_nonpos hneg)
    rw [map_smul, smul_eq_mul] at hh
    change -r * w v ≤ f q at hh
    linarith
  have hsum : 0 < ∑ v, w v := by
    apply Finset.sum_pos'
    · exact fun v _ => hw v
    · by_contra! h
      apply hf
      ext z
      rw [eval]
      simp [fun v => le_antisymm (h v (Finset.mem_univ v)) (hw v)]
  have hevalq : f q = (∑ v, w v) / t := by
    rw [eval]
    simp [q, ← Finset.mul_sum, div_eq_inv_mul]
  refine ⟨fun v => t * w v / ∑ i, w i, ⟨fun v => div_nonneg (mul_nonneg ht.le (hw v)) hsum.le,
    fun d a c ha => ?_⟩, ?_⟩
  · have h := hsep _ (cost_mem_costMinorants ha c)
    rw [eval (fun v => cost c (a v)), hevalq, le_div_iff₀ ht] at h
    calc
      ∑ v, cost c (a v) * (t * w v / ∑ i, w i) =
          ((∑ v, cost c (a v) * w v) * t) / ∑ i, w i := by
        rw [Finset.sum_mul, Finset.sum_div]
        exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ 1 := (div_le_one hsum).mpr h
  · rw [← Finset.sum_div, ← Finset.mul_sum, mul_div_cancel_right₀ _ hsum.ne']

private theorem sum_le_of_feasible {x : V → ℝ} (hx : x ∈ th G) {t : ℝ}
    (ht : t ∈ thetaFeasible G) : ∑ v, x v ≤ t := by
  obtain ⟨ht, d, a, c, -, ha, hv⟩ := ht
  calc
    ∑ v, x v ≤ ∑ v, (t * cost c (a v)) * x v :=
      Finset.sum_le_sum fun v _ => le_mul_of_one_le_left (hx.1 v) (hv v)
    _ = t * ∑ v, cost c (a v) * x v := by simp only [Finset.mul_sum, mul_assoc]
    _ ≤ t := mul_le_of_le_one_right ht (hx.2 d a c ha)

end

/-- **Theta is the maximum of the coordinate sum over the theta body.** For a finite graph `G`,
`ϑ(G) = sup {∑_v x_v : x ∈ TH(G)}` (Knuth, *The Sandwich Theorem*, 1994, eq. (5.1) with unit
weights: `ϑ = ϑ₁`, the theorem of Grötschel, Lovász and Schrijver that Knuth proves in §§5-12).
Knuth measures costs against the first coordinate vector, here any handle is allowed; an
orthogonal change of coordinates (Knuth, Lemma 0) shows that both choices give the same `TH(G)`
and the same `ϑ(G)`. -/
theorem lovaszTheta_eq_sSup_th {V : Type*} [Fintype V] (G : SimpleGraph V) :
    lovaszTheta G = sSup ((fun x : V → ℝ => ∑ v, x v) '' th G) := by
  have hzero : (0 : V → ℝ) ∈ th G := ⟨le_rfl, by simp⟩
  let S := (fun x : V → ℝ => ∑ v, x v) '' th G
  have h0 : 0 ∈ S := ⟨0, hzero, by simp⟩
  obtain ⟨k, hk⟩ : (thetaFeasible G).Nonempty :=
    ⟨_, natCast_mem_thetaFeasible_of_colorable Gᶜ.colorable_chromaticNumber_of_fintype⟩
  have upper_bound {t : ℝ} (ht : t ∈ thetaFeasible G) : t ∈ upperBounds S := by
    rintro _ ⟨x, hx, rfl⟩
    exact sum_le_of_feasible hx ht
  have hb : BddAbove S := ⟨k, upper_bound hk⟩
  refine le_antisymm ?_ (le_csInf ⟨k, hk⟩ fun t ht => csSup_le ⟨0, h0⟩ (upper_bound ht))
  by_contra! h
  obtain ⟨t, hSt, ht⟩ := exists_between h
  obtain ⟨x, hx, hsum⟩ := exists_mem_th_sum_eq ((le_csSup hb h0).trans_lt hSt) ht
  exact hSt.not_ge (le_csSup hb ⟨x, hx, hsum⟩)

end MathlibExt.Combinatorics.SimpleGraph.LovaszThetaBodyWanted
