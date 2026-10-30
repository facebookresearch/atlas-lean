/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

open scoped InnerProductSpace

namespace MathlibExt.Analysis.InnerProductSpace.Stampacchia

/-!
# Stampacchia's theorem for variational inequalities

Let `E` be a real Hilbert space, `K ⊆ E` a nonempty closed convex set,
`A : E →L[ℝ] E` a coercive bounded linear operator, `α * ‖u‖ ^ 2 ≤ ⟪A u, u⟫_ℝ`
with `α > 0`, and `f ∈ E`. Stampacchia's theorem states that there is exactly
one `u ∈ K` satisfying the variational inequality

  `⟪A u - f, v - u⟫_ℝ ≥ 0` for all `v ∈ K`.

The proof is the classical contraction argument: for a small step `ρ > 0` the
map `Φ x = P_K (x - ρ • (A x - f))` is a contraction, where `P_K` is the
nearest-point projection onto `K`, and a fixed point of `Φ` is exactly a
solution of the variational inequality by the variational characterization of
the projection. The bilinear-form version follows by representing the form
through the Riesz map `InnerProductSpace.toDual`.

This is a companion to the v1 book's Hilbert-space material
(`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean`): the book
proves the projection onto a closed subspace, which is already in Mathlib as
`orthogonalProjectionOnto`. Stampacchia's theorem itself is not one of the
72 v1 targets and is not in Mathlib. The nearest-point projection onto a
convex set is reproved here only in the minimal private form this proof
needs (existence, the variational characterization, nonexpansiveness);
it is not the public convex-projection API of an earlier batch.

Source: G. Stampacchia, *Formes bilinéaires coercitives sur les ensembles
convexes*, C. R. Acad. Sci. Paris 258 (1964), 4413–4416. See also H. Brezis,
*Functional Analysis, Sobolev Spaces and PDEs*, Springer (2011), Theorem 5.6.

Main results:

* `exists_unique_stampacchia`: Stampacchia's theorem, operator form.
* `exists_unique_stampacchia_bilinear`: Stampacchia's theorem, bilinear-form
  form, with a right-hand side given by a continuous linear functional.
* `stampacchia_eq_of_univ`: on the whole space a variational-inequality
  solution satisfies `A u = f`.
* `exists_eq_of_coercive`: a coercive bounded linear operator on a real
  Hilbert space is surjective.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Nearest point in a nonempty complete convex set, chosen once and for all.
Private: only the properties below are used, and only for Stampacchia's
theorem. -/
private noncomputable def stampacchiaProj {K : Set E} (hKne : K.Nonempty)
    (hKcomp : IsComplete K) (hKconv : Convex ℝ K) (x : E) : E :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex hKne hKcomp hKconv x)

/-- The nearest point lies in `K`. -/
private theorem stampacchiaProj_mem {K : Set E} (hKne : K.Nonempty)
    (hKcomp : IsComplete K) (hKconv : Convex ℝ K) (x : E) :
    stampacchiaProj hKne hKcomp hKconv x ∈ K :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hKne hKcomp hKconv x)).1

/-- The nearest point attains the infimum distance. -/
private theorem stampacchiaProj_norm_eq {K : Set E} (hKne : K.Nonempty)
    (hKcomp : IsComplete K) (hKconv : Convex ℝ K) (x : E) :
    ‖x - stampacchiaProj hKne hKcomp hKconv x‖ = ⨅ w : K, ‖x - w‖ :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hKne hKcomp hKconv x)).2

/-- Variational characterization of the nearest point. -/
private theorem stampacchiaProj_variational {K : Set E} (hKne : K.Nonempty)
    (hKcomp : IsComplete K) (hKconv : Convex ℝ K) {x : E} {w : E} (hw : w ∈ K) :
    ⟪x - stampacchiaProj hKne hKcomp hKconv x,
      w - stampacchiaProj hKne hKcomp hKconv x⟫_ℝ ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero hKconv
    (stampacchiaProj_mem hKne hKcomp hKconv x)).mp
    (stampacchiaProj_norm_eq hKne hKcomp hKconv x) w hw

/-- The nearest-point projection is nonexpansive. -/
private theorem norm_stampacchiaProj_sub_le {K : Set E} (hKne : K.Nonempty)
    (hKcomp : IsComplete K) (hKconv : Convex ℝ K) (x y : E) :
    ‖stampacchiaProj hKne hKcomp hKconv x - stampacchiaProj hKne hKcomp hKconv y‖
      ≤ ‖x - y‖ := by
  set px := stampacchiaProj hKne hKcomp hKconv x with hpx
  set py := stampacchiaProj hKne hKcomp hKconv y with hpy
  have hpxK : px ∈ K := stampacchiaProj_mem hKne hKcomp hKconv x
  have hpyK : py ∈ K := stampacchiaProj_mem hKne hKcomp hKconv y
  have h1 := stampacchiaProj_variational hKne hKcomp hKconv (x := x) (w := py) hpyK
  have h2 := stampacchiaProj_variational hKne hKcomp hKconv (x := y) (w := px) hpxK
  have hge1 : 0 ≤ ⟪x - px, px - py⟫_ℝ := by
    have h := h1
    rw [show py - px = -(px - py) by abel, inner_neg_right] at h
    linarith
  have hge2 : 0 ≤ ⟪y - py, py - px⟫_ℝ := by
    have h := h2
    rw [show px - py = -(py - px) by abel, inner_neg_right] at h
    linarith
  have hident : ⟪x - y, px - py⟫_ℝ
      = ‖px - py‖ ^ 2 + ⟪x - px, px - py⟫_ℝ + ⟪y - py, py - px⟫_ℝ := by
    have e : x - y = (x - px) + (px - py) + (py - y) := by abel
    rw [e, inner_add_left, inner_add_left, real_inner_self_eq_norm_sq]
    have hneg : ⟪py - y, px - py⟫_ℝ = ⟪y - py, py - px⟫_ℝ := by
      rw [show py - y = -(y - py) by abel, show px - py = -(py - px) by abel,
        inner_neg_left, inner_neg_right, neg_neg]
    rw [hneg]
    ring
  have key : ‖px - py‖ ^ 2 ≤ ⟪x - y, px - py⟫_ℝ := by linarith
  have hcs := real_inner_le_norm (x - y) (px - py)
  by_cases hd : ‖px - py‖ = 0
  · rw [hd]
    exact norm_nonneg _
  · have hpos : 0 < ‖px - py‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
    have hle : ‖px - py‖ * ‖px - py‖ ≤ ‖x - y‖ * ‖px - py‖ := by
      rw [← sq]
      exact key.trans hcs
    exact le_of_mul_le_mul_right hle hpos

/-- The contraction map whose fixed points are the variational-inequality
solutions: `Φ x = P_K (x - ρ • (A x - f))`. -/
private noncomputable def stampacchiaPhi {K : Set E} (hKne : K.Nonempty)
    (hKcomp : IsComplete K) (hKconv : Convex ℝ K) (A : E →L[ℝ] E) (ρ : ℝ) (f : E)
    (x : E) : E :=
  stampacchiaProj hKne hKcomp hKconv (x - ρ • (A x - f))

/-- On the whole space, a variational-inequality solution satisfies `A u = f`. -/
theorem stampacchia_eq_of_univ (A : E →L[ℝ] E) (f : E) (u : E)
    (h : ∀ v ∈ (Set.univ : Set E), 0 ≤ ⟪A u - f, v - u⟫_ℝ) : A u = f := by
  have h1 := h (u + (A u - f)) (Set.mem_univ _)
  have h2 := h (u - (A u - f)) (Set.mem_univ _)
  have e1 : ⟪A u - f, (u + (A u - f)) - u⟫_ℝ = ⟪A u - f, A u - f⟫_ℝ := by
    congr 1
    abel
  have e2 : ⟪A u - f, (u - (A u - f)) - u⟫_ℝ = -⟪A u - f, A u - f⟫_ℝ := by
    rw [show (u - (A u - f)) - u = -(A u - f) by abel, inner_neg_right]
  rw [e1] at h1
  rw [e2] at h2
  have hself : ⟪A u - f, A u - f⟫_ℝ = 0 := by linarith
  rw [real_inner_self_eq_norm_sq] at hself
  have hnorm : ‖A u - f‖ = 0 := sq_eq_zero_iff.mp hself
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

variable [CompleteSpace E]

/-- **Stampacchia's theorem, operator form.** For a coercive bounded linear
operator `A` on a real Hilbert space, a nonempty closed convex set `K`, and
`f ∈ E`, there is exactly one `u ∈ K` with `⟪A u - f, v - u⟫_ℝ ≥ 0` for all
`v ∈ K`. -/
theorem exists_unique_stampacchia {K : Set E} (hKne : K.Nonempty)
    (hKclosed : IsClosed K) (hKconv : Convex ℝ K) (A : E →L[ℝ] E) {α : ℝ}
    (hα : 0 < α) (hcoer : ∀ u, α * ‖u‖ ^ 2 ≤ ⟪A u, u⟫_ℝ) (f : E) :
    ∃! u, u ∈ K ∧ ∀ v ∈ K, 0 ≤ ⟪A u - f, v - u⟫_ℝ := by
  rcases subsingleton_or_nontrivial E with hsub | hnt
  · obtain ⟨u₀, hu₀⟩ := hKne
    refine ⟨u₀, ⟨hu₀, ?_⟩, ?_⟩
    · intro v hv
      have hv0 : v = u₀ := Subsingleton.elim v u₀
      rw [hv0, sub_self, inner_zero_right]
    · intro u' _
      exact Subsingleton.elim u' u₀
  · have hKcomp : IsComplete K := hKclosed.isComplete
    have hKne0 : K.Nonempty := hKne
    -- A unit vector shows `α ≤ ‖A‖`.
    have hα_le : α ≤ ‖A‖ := by
      obtain ⟨u, hu⟩ : ∃ u : E, ‖u‖ = 1 := by
        obtain ⟨u, hu⟩ := exists_ne (0 : E)
        exact ⟨‖u‖⁻¹ • u, by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
            inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)]⟩
      have h1 := hcoer u
      have h2 := real_inner_le_norm (A u) u
      have h3 := A.le_opNorm u
      simp only [hu, mul_one, one_pow] at h1 h2 h3
      exact h1.trans (h2.trans h3)
    set s : ℝ := ‖A‖ ^ 2 with hsdef
    have hs_nonneg : 0 ≤ s := hsdef ▸ sq_nonneg ‖A‖
    have hD : 0 < s + α ^ 2 := add_pos_of_nonneg_of_pos hs_nonneg (pow_pos hα 2)
    have hD2 : 0 < (s + α ^ 2) ^ 2 := pow_pos hD 2
    set ρ : ℝ := α / (s + α ^ 2) with hρdef
    have hρpos : 0 < ρ := hρdef ▸ div_pos hα hD
    set F : ℝ := 1 - 2 * ρ * α + ρ ^ 2 * s with hFdef
    -- `F * (s + α ^ 2) ^ 2 = s ^ 2 + α ^ 2 * s - α ^ 4`, by clearing the denominator.
    have hmul : F * (s + α ^ 2) ^ 2 = s ^ 2 + α ^ 2 * s - α ^ 4 := by
      rw [hFdef, hρdef]
      field_simp
      ring
    have hfactor_nonneg : 0 ≤ F := by
      have hnum : 0 ≤ s ^ 2 + α ^ 2 * s - α ^ 4 := by
        have hα2 : α ^ 2 ≤ s := by
          have h := pow_le_pow_left₀ (le_of_lt hα) hα_le 2
          rwa [← hsdef] at h
        have h1 : α ^ 4 ≤ s ^ 2 := by
          calc α ^ 4 = (α ^ 2) ^ 2 := by ring
            _ ≤ s ^ 2 := pow_le_pow_left₀ (pow_nonneg (le_of_lt hα) 2) hα2 2
        nlinarith [mul_nonneg (sq_nonneg α) hs_nonneg, h1]
      nlinarith [hmul, hnum, hD2]
    have hfactor_lt : F < 1 := by
      have hlt : s ^ 2 + α ^ 2 * s - α ^ 4 < (s + α ^ 2) ^ 2 := by
        nlinarith [mul_nonneg (sq_nonneg α) hs_nonneg, pow_pos hα 4]
      nlinarith [hmul, hlt, hD2]
    set q : ℝ := Real.sqrt F with hqdef
    have hq0 : 0 ≤ q := hqdef ▸ Real.sqrt_nonneg F
    have hq1 : q < 1 := by
      have h : Real.sqrt F < Real.sqrt 1 := Real.sqrt_lt_sqrt hfactor_nonneg hfactor_lt
      rwa [Real.sqrt_one] at h
    -- `Φ` is a contraction of constant `q`.
    have hΦlip : LipschitzWith ⟨q, hq0⟩
        (stampacchiaPhi hKne hKcomp hKconv A ρ f) :=
      LipschitzWith.of_dist_le_mul (fun x y => by
        rw [dist_eq_norm, dist_eq_norm]
        have h1 : ‖stampacchiaPhi hKne hKcomp hKconv A ρ f x
            - stampacchiaPhi hKne hKcomp hKconv A ρ f y‖
            ≤ ‖(x - ρ • (A x - f)) - (y - ρ • (A y - f))‖ :=
          norm_stampacchiaProj_sub_le hKne hKcomp hKconv _ _
        have hdiff : (x - ρ • (A x - f)) - (y - ρ • (A y - f))
            = (x - y) - ρ • A (x - y) := by
          rw [map_sub]
          simp only [smul_sub]
          abel
        rw [hdiff] at h1
        have h2 : ‖(x - y) - ρ • A (x - y)‖ ≤ q * ‖x - y‖ := by
          have hnormsq : ‖(x - y) - ρ • A (x - y)‖ ^ 2 ≤ F * ‖x - y‖ ^ 2 := by
            rw [hFdef, norm_sub_sq_real]
            have hinner : ⟪x - y, ρ • A (x - y)⟫_ℝ
                = ρ * ⟪A (x - y), x - y⟫_ℝ := by
              rw [inner_smul_right, real_inner_comm]
            have hnorm : ‖ρ • A (x - y)‖ ^ 2 = ρ ^ 2 * ‖A (x - y)‖ ^ 2 := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρpos]
              ring
            rw [hinner, hnorm]
            have hco := hcoer (x - y)
            have hAd2 : ‖A (x - y)‖ ^ 2 ≤ s * ‖x - y‖ ^ 2 := by
              calc ‖A (x - y)‖ ^ 2 ≤ (‖A‖ * ‖x - y‖) ^ 2 :=
                    pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) 2
                _ = s * ‖x - y‖ ^ 2 := by rw [hsdef]; ring
            have hρ1 : 0 ≤ ρ * (⟪A (x - y), x - y⟫_ℝ - α * ‖x - y‖ ^ 2) :=
              mul_nonneg hρpos.le (sub_nonneg.mpr hco)
            have hρ2 : 0 ≤ ρ ^ 2 * (s * ‖x - y‖ ^ 2 - ‖A (x - y)‖ ^ 2) :=
              mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hAd2)
            nlinarith [hρ1, hρ2]
          have hq2 : q ^ 2 = F := by rw [hqdef]; exact Real.sq_sqrt hfactor_nonneg
          have hsq : ‖(x - y) - ρ • A (x - y)‖ ^ 2 ≤ (q * ‖x - y‖) ^ 2 := by
            calc ‖(x - y) - ρ • A (x - y)‖ ^ 2 ≤ F * ‖x - y‖ ^ 2 := hnormsq
              _ = (q * ‖x - y‖) ^ 2 := by rw [← hq2]; ring
          have h := sq_le_sq.mp hsq
          rwa [abs_of_nonneg (norm_nonneg _),
            abs_of_nonneg (mul_nonneg hq0 (norm_nonneg _))] at h
        exact h1.trans h2)
    have hcon : ContractingWith ⟨q, hq0⟩
        (stampacchiaPhi hKne hKcomp hKconv A ρ f) :=
      ⟨by exact_mod_cast hq1, hΦlip⟩
    obtain ⟨u₀, hu₀⟩ := hKne
    obtain ⟨u, hufix, -, -⟩ := hcon.exists_fixedPoint u₀ (edist_ne_top _ _)
    have hproj_eq : stampacchiaProj hKne0 hKcomp hKconv (u - ρ • (A u - f)) = u :=
      hufix
    have huK : u ∈ K :=
      hproj_eq ▸ stampacchiaProj_mem hKne0 hKcomp hKconv (u - ρ • (A u - f))
    have hVI : ∀ v ∈ K, 0 ≤ ⟪A u - f, v - u⟫_ℝ := by
      intro v hv
      have hvar := stampacchiaProj_variational hKne0 hKcomp hKconv (x := u - ρ • (A u - f))
        (w := v) hv
      rw [hproj_eq] at hvar
      have hsimpl : (u - ρ • (A u - f)) - u = -(ρ • (A u - f)) := by module
      rw [hsimpl, inner_neg_left, inner_smul_left] at hvar
      simp only [starRingEnd_apply, star_trivial] at hvar
      have hnn : 0 ≤ ρ * ⟪A u - f, v - u⟫_ℝ := by linarith [hvar]
      exact nonneg_of_mul_nonneg_right hnn hρpos
    refine ⟨u, ⟨huK, hVI⟩, ?_⟩
    intro u' hu'
    obtain ⟨hu'K, hVI'⟩ := hu'
    -- Uniqueness from coercivity: test each solution against the other.
    have h1 := hVI u' hu'K
    have h2 := hVI' u huK
    have hdecomp : A u' - f = (A u - f) - A (u - u') := by rw [map_sub]; abel
    rw [hdecomp, inner_sub_left] at h2
    -- `h2 : 0 ≤ ⟪A u - f, u - u'⟫ - ⟪A (u - u'), u - u'⟫`
    have hneg : ⟪A u - f, u' - u⟫_ℝ = -⟪A u - f, u - u'⟫_ℝ := by
      rw [show u' - u = -(u - u') by abel, inner_neg_right]
    rw [hneg] at h1
    -- `h1 : 0 ≤ -⟪A u - f, u - u'⟫`, so `⟪A (u - u'), u - u'⟫ ≤ 0`.
    have hle : ⟪A (u - u'), u - u'⟫_ℝ ≤ 0 := by linarith [h1, h2]
    have hco := hcoer (u - u')
    have hnorm : ‖u - u'‖ = 0 := by
      have hsq : ‖u - u'‖ ^ 2 ≤ 0 := by nlinarith [hle, hco, hα]
      exact sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))
    exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm

/-- **Stampacchia's theorem, bilinear-form form.** For a coercive bounded
bilinear form `B` on a real Hilbert space, a nonempty closed convex set `K`,
and a continuous linear functional `φ`, there is exactly one `u ∈ K` with
`B u (v - u) ≥ φ (v - u)` for all `v ∈ K`. -/
theorem exists_unique_stampacchia_bilinear {K : Set E} (hKne : K.Nonempty)
    (hKclosed : IsClosed K) (hKconv : Convex ℝ K)
    (B : E →L[ℝ] E →L[ℝ] ℝ) {α : ℝ} (hα : 0 < α)
    (hcoer : ∀ u, α * ‖u‖ ^ 2 ≤ B u u) (φ : E →L[ℝ] ℝ) :
    ∃! u, u ∈ K ∧ ∀ v ∈ K, φ (v - u) ≤ B u (v - u) := by
  -- Represent `B` and `φ` by vectors through the Riesz map. For `B` this is
  -- Mathlib's `continuousLinearMapOfBilin`, as used for Lax–Milgram.
  let A : E →L[ℝ] E := InnerProductSpace.continuousLinearMapOfBilin (𝕜 := ℝ) B
  have hA : ∀ u v : E, ⟪A u, v⟫_ℝ = B u v := by
    intro u v
    exact InnerProductSpace.continuousLinearMapOfBilin_apply B u v
  let f : E := (InnerProductSpace.toDual ℝ E).symm φ
  have hf : ∀ v : E, ⟪f, v⟫_ℝ = φ v := by
    intro v
    have h := InnerProductSpace.toDual_symm_apply (E := E) (𝕜 := ℝ) (x := v) (y := φ)
    exact h
  have hcoerA : ∀ u, α * ‖u‖ ^ 2 ≤ ⟪A u, u⟫_ℝ := by
    intro u
    rw [hA]
    exact hcoer u
  obtain ⟨u, ⟨huK, hVI⟩, huniq⟩ :=
    exists_unique_stampacchia hKne hKclosed hKconv A hα hcoerA f
  refine ⟨u, ⟨huK, ?_⟩, ?_⟩
  · intro v hv
    have h := hVI v hv
    rw [inner_sub_left, hA, hf] at h
    linarith [h]
  · intro u' hu'
    obtain ⟨hu'K, hVI'⟩ := hu'
    apply huniq
    refine ⟨hu'K, ?_⟩
    intro v hv
    have h := hVI' v hv
    rw [inner_sub_left, hA, hf]
    linarith [h]


/-- A coercive bounded linear operator on a real Hilbert space is surjective.
This is the whole-space case of Stampacchia's theorem (compare Mathlib's
Lax–Milgram theorem, which is the analogous statement for bilinear forms). -/
theorem exists_eq_of_coercive (A : E →L[ℝ] E) {α : ℝ} (hα : 0 < α)
    (hcoer : ∀ u, α * ‖u‖ ^ 2 ≤ ⟪A u, u⟫_ℝ) (f : E) : ∃ u, A u = f := by
  obtain ⟨u, ⟨-, hVI⟩, -⟩ := exists_unique_stampacchia Set.univ_nonempty isClosed_univ
    convex_univ A hα hcoer f
  exact ⟨u, stampacchia_eq_of_univ A f u hVI⟩

end MathlibExt.Analysis.InnerProductSpace.Stampacchia
