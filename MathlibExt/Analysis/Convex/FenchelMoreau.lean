/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Constructions

@[expose] public section

namespace MathlibExt.Analysis.Convex.FenchelMoreau

/-!
# Fenchel conjugates and epigraph API

Foundation for the Fenchel–Moreau theorem: a proper lsc convex
`f : E → EReal` on a Hausdorff locally convex real tvs equals its
biconjugate. This module provides the conjugate/biconjugate definitions in
the exact shape of `banach_limit`-style wanted statements and the
closed-epigraph API (convexity is definitional from the hypothesis;
closedness is the continuous preimage of the `EReal` epigraph).

References: Werner Fenchel, *Convex Cones, Sets, and Functions: From Notes
by D. W. Blackett of Lectures at Princeton University, 1951*, Princeton
University Department of Mathematics, 1953, Open Library OL1430688W; and
Jean-Jacques Moreau, "Fonctions convexes duales et points proximaux,"
C. R. Acad. Sci. Paris 255 (1962), 2897–2899, zbMATH 0118.10502.
-/

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E]

/-- **Fenchel conjugate.** Let $E$ be a real vector space with a topology and let
$f : E \to [-\infty, \infty]$. The Fenchel conjugate of $f$ at a continuous linear functional
$L : E \to \mathbb{R}$ is the extended real number $f^*(L) = \sup_{y \in E} \big(L(y) - f(y)\big)$.
-/
noncomputable def fenchelConj (f : E → EReal) (L : E →L[ℝ] ℝ) : EReal :=
  ⨆ y : E, (((L y : ℝ)) : EReal) - f y

/-- **Fenchel biconjugate.** Let $E$ be a real vector space with a topology and let
$f : E \to [-\infty, \infty]$. The biconjugate of $f$ at $x \in E$ is the extended real number
$f^{**}(x) = \sup_L \big(L(x) - f^*(L)\big)$, where $L$ ranges over the continuous linear
functionals $E \to \mathbb{R}$ and $f^*$ is the Fenchel conjugate of $f$. -/
noncomputable def fenchelBiconj (f : E → EReal) (x : E) : EReal :=
  ⨆ L : E →L[ℝ] ℝ, (((L x : ℝ)) : EReal) - fenchelConj f L

omit [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [T2Space E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
/-- The `ℝ`-threshold epigraph is the preimage of the `EReal` epigraph. -/
private lemma epi_eq_preimage (f : E → EReal) :
    {p : E × ℝ | f p.1 ≤ (p.2 : EReal)}
      = (fun p : E × ℝ => (p.1, ((p.2 : ℝ) : EReal))) ⁻¹'
        {q : E × EReal | f q.1 ≤ q.2} := by
  ext ⟨x, r⟩
  rfl

omit [AddCommGroup E] [Module ℝ E] [T2Space E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
/-- **Lower semicontinuous functions have closed epigraphs.** Let $E$ be a topological space and
let $f : E \to [-\infty, \infty]$ be lower semicontinuous. Then the set
$\{(x, r) \in E \times \mathbb{R} : f(x) \le r\}$ is closed in $E \times \mathbb{R}$. -/
theorem isClosed_epi_real (f : E → EReal) (hf_lsc : LowerSemicontinuous f) :
    IsClosed {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
  rw [epi_eq_preimage]
  apply IsClosed.preimage _ hf_lsc.isClosed_epigraph
  exact continuous_fst.prodMk
    (EReal.continuous_coe_iff.mpr continuous_snd)

omit [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] in
/-- **The biconjugate lies below the function.** Let $E$ be a real vector space with a topology
and let $f : E \to [-\infty, \infty]$ never take the value $-\infty$. Then $f^{**}(x) \le f(x)$
for every $x \in E$, where $f^{**}$ is the Fenchel biconjugate of $f$.

This is the easy direction of the Fenchel–Moreau theorem. -/
theorem biconj_le (f : E → EReal) (hf_not_bot : ∀ x, f x ≠ ⊥) (x : E) :
    fenchelBiconj f x ≤ f x := by
  unfold fenchelBiconj
  apply ciSup_le
  intro L
  by_cases hfx : f x = ⊤
  · rw [hfx]
    exact le_top
  · apply EReal.sub_le_of_le_add
    have h1 : (((L x : ℝ)) : EReal) - f x ≤ fenchelConj f L := by
      unfold fenchelConj
      exact le_iSup (fun y => (((L y : ℝ)) : EReal) - f y) x
    have h2 : f x + ((((L x : ℝ)) : EReal) - f x)
        ≤ f x + fenchelConj f L :=
      add_le_add le_rfl h1
    have h3 : (((L x : ℝ)) : EReal) = f x + ((((L x : ℝ)) : EReal) - f x) := by
      lift f x to ℝ using ⟨hfx, hf_not_bot x⟩ with s
      rw [← EReal.coe_sub, ← EReal.coe_add]
      congr 1
      ring
    rw [h3]
    exact h2

/-- Effective domain: points where `f` is not `⊤`. -/
private def dom (f : E → EReal) : Set E := {y | f y ≠ ⊤}

omit [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [T2Space E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
/-- Epigraph points project into the domain. -/
private lemma epi_fst_mem (f : E → EReal) (y : E) (s : ℝ)
    (h : f y ≤ (s : EReal)) : y ∈ dom f := by
  change f y ≠ ⊤
  intro htop
  rw [htop] at h
  exact (EReal.coe_lt_top s).not_ge h

omit [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [T2Space E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
/-- Domain points lift to epigraph points (using `f ≠ ⊥`). -/
private lemma dom_mem_epi (f : E → EReal) (hf_not_bot : ∀ x, f x ≠ ⊥)
    (y : E) (hy : y ∈ dom f) : ∃ s : ℝ, f y ≤ (s : EReal) := by
  lift f y to ℝ using ⟨hy, hf_not_bot y⟩ with t
  exact ⟨t, le_rfl⟩

omit [TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
/-- The domain is convex. -/
private lemma convex_dom (f : E → EReal)
    (hf_convex : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)})
    (hf_not_bot : ∀ x, f x ≠ ⊥) : Convex ℝ (dom f) := by
  have e : dom f = LinearMap.fst ℝ E ℝ '' {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    ext y
    constructor
    · intro hy
      obtain ⟨s, hs⟩ := dom_mem_epi f hf_not_bot y hy
      exact ⟨(y, s), hs, rfl⟩
    · rintro ⟨⟨a, b⟩, hab, rfl⟩
      exact epi_fst_mem f a b hab
  rw [e]
  exact hf_convex.linear_image _

omit [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] in
/-- A separator with negative vertical slope yields a pointwise minorant. -/
private lemma sep_minorant_le (f : E → EReal) (hf_not_bot : ∀ x, f x ≠ ⊥)
    (L : E →L[ℝ] ℝ) (c u : ℝ) (hc : c < 0)
    (hsep : ∀ (y : E) (s : ℝ), f y ≤ (s : EReal) → L y + s * c < u)
    (y : E) : ((((L y - u) / (-c) : ℝ)) : EReal) ≤ f y := by
  by_cases hfy : f y = ⊤
  · rw [hfy]
    exact le_top
  · obtain ⟨t, ht⟩ : ∃ t : ℝ, ((t : ℝ) : EReal) = f y :=
      ⟨(f y).toReal, EReal.coe_toReal hfy (hf_not_bot y)⟩
    rw [← ht]
    have hmem : f y ≤ (t : EReal) := by rw [← ht]
    have h := hsep y t hmem
    have dpos : 0 < -c := neg_pos.mpr hc
    have key : L y - u < t * (-c) := by
      have htc : t * (-c) = -(t * c) := by ring
      rw [htc]
      linarith [h]
    have hlt : (L y - u) / (-c) < t := by
      rw [div_lt_iff₀ dpos]
      exact key
    exact le_of_lt (EReal.coe_lt_coe_iff.mpr hlt)

omit [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] in
/-- The minorant exceeds `a'` at the separated point. -/
private lemma sep_minorant_pt (L : E →L[ℝ] ℝ) (c u a' : ℝ) (x₀ : E)
    (hc : c < 0) (hpt : u < L x₀ + a' * c) :
    a' < (L x₀ - u) / (-c) := by
  have dpos : 0 < -c := neg_pos.mpr hc
  rw [lt_div_iff₀ dpos]
  have hac : a' * (-c) = -(a' * c) := by ring
  rw [hac]
  linarith [hpt]

omit [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] in
/-- A separator with negative vertical slope yields a dual lower bound. -/
private lemma dual_bound_of_sep (f : E → EReal) (hf_not_bot : ∀ x, f x ≠ ⊥)
    (x₀ : E) (a a' : ℝ) (haa' : a < a')
    (L : E →L[ℝ] ℝ) (c u : ℝ) (hc : c < 0)
    (hsep : ∀ (y : E) (s : ℝ), f y ≤ (s : EReal) → L y + s * c < u)
    (hpt : u < L x₀ + a' * c) :
    ∃ L' : E →L[ℝ] ℝ,
      (a : EReal) ≤ ((((L' x₀ : ℝ))) : EReal) - fenchelConj f L' := by
  refine ⟨(-c)⁻¹ • L, ?_⟩
  set L' : E →L[ℝ] ℝ := (-c)⁻¹ • L with hL'def
  have dpos : 0 < -c := neg_pos.mpr hc
  have dne : -c ≠ 0 := ne_of_gt dpos
  have hL' : ∀ z : E, L' z = (-c)⁻¹ * L z := fun z => rfl
  have hm : ∀ z : E, ((((L z - u) / (-c) : ℝ)) : EReal) ≤ f z :=
    fun z => sep_minorant_le f hf_not_bot L c u hc hsep z
  have hmpt : a' < (L x₀ - u) / (-c) := sep_minorant_pt L c u a' x₀ hc hpt
  have hconj : fenchelConj f L' ≤ (((u / (-c) : ℝ)) : EReal) := by
    unfold fenchelConj
    apply ciSup_le
    intro z
    have h1 : ((((L' z : ℝ))) : EReal) - f z
        ≤ ((((L' z : ℝ))) : EReal) - ((((L z - u) / (-c) : ℝ)) : EReal) :=
      EReal.sub_le_sub le_rfl (hm z)
    have h2 : ((((L' z : ℝ))) : EReal) - ((((L z - u) / (-c) : ℝ)) : EReal)
        = (((u / (-c) : ℝ)) : EReal) := by
      rw [← EReal.coe_sub]
      congr 1
      rw [hL' z]
      field_simp
      ring
    rw [h2] at h1
    exact h1
  have hfin : ((((L' x₀ : ℝ))) : EReal) - (((u / (-c) : ℝ)) : EReal)
      = ((((L x₀ - u) / (-c) : ℝ)) : EReal) := by
    rw [← EReal.coe_sub]
    congr 1
    rw [hL' x₀]
    field_simp
    ring
  have hle : ((((L' x₀ : ℝ))) : EReal) - (((u / (-c) : ℝ)) : EReal)
      ≤ ((((L' x₀ : ℝ))) : EReal) - fenchelConj f L' :=
    EReal.sub_le_sub le_rfl hconj
  rw [hfin] at hle
  have ha : (a : EReal) < ((((L x₀ - u) / (-c) : ℝ)) : EReal) := by
    rw [EReal.coe_lt_coe_iff]
    exact lt_trans haa' hmpt
  exact le_trans (le_of_lt ha) hle

omit [T2Space E] in
/-- Separate a point strictly below the graph; vertical slope is nonpositive. -/
private lemma separate_epi (f : E → EReal)
    (hf_convex : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)})
    (hf_lsc : LowerSemicontinuous f)
    (hf_not_top : ∃ x, f x ≠ ⊤)
    (hf_not_bot : ∀ x, f x ≠ ⊥)
    (x₀ : E) (a' : ℝ) (ha'fx : (a' : EReal) < f x₀) :
    ∃ (L : E →L[ℝ] ℝ) (c u : ℝ), c ≤ 0
      ∧ (∀ (y : E) (s : ℝ), f y ≤ (s : EReal) → L y + s * c < u)
      ∧ u < L x₀ + a' * c := by
  have hpt_mem : (x₀, a') ∉ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    intro h
    have h' : f x₀ ≤ (a' : EReal) := h
    exact lt_irrefl _ (lt_of_le_of_lt h' ha'fx)
  obtain ⟨φ, u, hφepi, hφpt⟩ := geometric_hahn_banach_closed_point
    hf_convex (isClosed_epi_real f hf_lsc) hpt_mem
  set L : E →L[ℝ] ℝ := φ.comp (ContinuousLinearMap.inl ℝ E ℝ) with hLdef
  set c : ℝ := φ (0, 1) with hcdef
  have hdecomp : ∀ (y : E) (s : ℝ), φ (y, s) = L y + s * c := by
    intro y s
    have e1 : (y, s) = (y, 0) + s • ((0, 1) : E × ℝ) := by
      ext <;> simp
    rw [e1, map_add, map_smul]
    rfl
  have hsep : ∀ (y : E) (s : ℝ), f y ≤ (s : EReal) → L y + s * c < u := by
    intro y s hs
    simpa [hdecomp] using hφepi (y, s) hs
  have hpt : u < L x₀ + a' * c := by
    simpa [hdecomp] using hφpt
  have hc_nonpos : c ≤ 0 := by
    by_contra hcon
    have hpos : 0 < c := not_le.mp hcon
    obtain ⟨x₁, hx₁⟩ := hf_not_top
    obtain ⟨μ₁, hμ₁⟩ : ∃ μ₁ : ℝ, ((μ₁ : ℝ) : EReal) = f x₁ :=
      ⟨(f x₁).toReal, EReal.coe_toReal hx₁ (hf_not_bot x₁)⟩
    have hmem : ∀ s : ℝ, μ₁ ≤ s → f x₁ ≤ (s : EReal) := by
      intro s hs
      rw [← hμ₁]
      exact EReal.coe_le_coe_iff.mpr hs
    have hray : ∀ s : ℝ, μ₁ ≤ s → L x₁ + s * c < u := fun s hs => hsep x₁ s (hmem s hs)
    have hbase : L x₁ + μ₁ * c < u := hray μ₁ le_rfl
    have hcne : c ≠ 0 := ne_of_gt hpos
    set t : ℝ := (u - L x₁ - μ₁ * c + 1) / c with ht
    have hnpos : 0 < u - L x₁ - μ₁ * c + 1 := by linarith [hbase]
    have ht0 : 0 ≤ t := le_of_lt (div_pos hnpos hpos)
    have htc : t * c = u - L x₁ - μ₁ * c + 1 := by
      rw [ht]
      field_simp
    have htop : L x₁ + (μ₁ + t) * c ≥ u := by
      have he : (μ₁ + t) * c = μ₁ * c + (u - L x₁ - μ₁ * c + 1) := by
        rw [add_mul, htc]
      linarith [he]
    have hcon' := hray (μ₁ + t) (le_add_of_nonneg_right ht0)
    linarith [hcon', htop]
  exact ⟨L, c, u, hc_nonpos, hsep, hpt⟩

omit [T2Space E] in
/-- Finite case: below a finite value, dual bounds approach `f x₀`. -/
private lemma finite_case (f : E → EReal)
    (hf_convex : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)})
    (hf_lsc : LowerSemicontinuous f)
    (hf_not_top : ∃ x, f x ≠ ⊤)
    (hf_not_bot : ∀ x, f x ≠ ⊥)
    (x₀ : E) (μ₀ : ℝ) (hμ₀ : f x₀ = (μ₀ : EReal))
    (a : ℝ) (ha : (a : EReal) < f x₀) :
    ∃ L' : E →L[ℝ] ℝ,
      (a : EReal) ≤ ((((L' x₀ : ℝ))) : EReal) - fenchelConj f L' := by
  have ham : a < μ₀ := by
    have h : (a : EReal) < (μ₀ : EReal) := by rwa [hμ₀] at ha
    exact EReal.coe_lt_coe_iff.mp h
  set a' : ℝ := (a + μ₀) / 2 with ha'def
  have haa' : a < a' := by rw [ha'def]; linarith [ham]
  have ha'fx : (a' : EReal) < f x₀ := by
    rw [hμ₀]
    apply EReal.coe_lt_coe_iff.mpr
    rw [ha'def]
    linarith [ham]
  obtain ⟨L, c, u, hc_nonpos, hsep, hpt⟩ := separate_epi f hf_convex hf_lsc
    hf_not_top hf_not_bot x₀ a' ha'fx
  have hc_ne : c ≠ 0 := by
    intro hcz
    have hmem : f x₀ ≤ ((μ₀ : ℝ) : EReal) := by rw [hμ₀]
    have h1 := hsep x₀ μ₀ hmem
    rw [hcz] at h1
    have h2 := hpt
    rw [hcz] at h2
    simp at h1 h2
    linarith [h1, h2]
  have hc : c < 0 := lt_of_le_of_ne hc_nonpos hc_ne
  exact dual_bound_of_sep f hf_not_bot x₀ a a' haa' L c u hc hsep hpt

omit [T2Space E] in
/-- Infinite case inside the domain closure: every separator has `c ≠ 0`. -/
private lemma closure_case (f : E → EReal)
    (hf_convex : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)})
    (hf_lsc : LowerSemicontinuous f)
    (hf_not_top : ∃ x, f x ≠ ⊤)
    (hf_not_bot : ∀ x, f x ≠ ⊥)
    (x₀ : E) (hfx : f x₀ = ⊤) (hx₀ : x₀ ∈ closure (dom f)) (a : ℝ) :
    ∃ L' : E →L[ℝ] ℝ,
      (a : EReal) ≤ ((((L' x₀ : ℝ))) : EReal) - fenchelConj f L' := by
  set a' : ℝ := a + 1 with ha'def
  have haa' : a < a' := by rw [ha'def]; linarith
  have ha'fx : (a' : EReal) < f x₀ := by
    rw [hfx]
    exact EReal.coe_lt_top _
  obtain ⟨L, c, u, hc_nonpos, hsep, hpt⟩ := separate_epi f hf_convex hf_lsc
    hf_not_top hf_not_bot x₀ a' ha'fx
  have hc_ne : c ≠ 0 := by
    intro hcz
    have hdom : ∀ y ∈ dom f, L y < u := by
      intro y hy
      obtain ⟨s, hs⟩ := dom_mem_epi f hf_not_bot y hy
      have h := hsep y s hs
      rw [hcz] at h
      simpa using h
    have hclosed : IsClosed {z : E | L z ≤ u} :=
      isClosed_le L.continuous continuous_const
    have hsub : dom f ⊆ {z : E | L z ≤ u} := fun z hz => le_of_lt (hdom z hz)
    have hclo : x₀ ∈ {z : E | L z ≤ u} := closure_minimal hsub hclosed hx₀
    have hle : L x₀ ≤ u := hclo
    have hgt : u < L x₀ := by
      have h := hpt
      rw [hcz] at h
      simpa using h
    exact lt_irrefl _ (lt_of_le_of_lt hle hgt)
  have hc : c < 0 := lt_of_le_of_ne hc_nonpos hc_ne
  exact dual_bound_of_sep f hf_not_bot x₀ a a' haa' L c u hc hsep hpt

omit [T2Space E] in
/-- Some direction has finite conjugate (from the finite case at `x₁`). -/
private lemma finite_conj_dir (f : E → EReal)
    (hf_convex : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)})
    (hf_lsc : LowerSemicontinuous f)
    (hf_not_top : ∃ x, f x ≠ ⊤)
    (hf_not_bot : ∀ x, f x ≠ ⊥) :
    ∃ M₀ : E →L[ℝ] ℝ, fenchelConj f M₀ < ⊤ := by
  obtain ⟨x₁, hx₁⟩ := hf_not_top
  obtain ⟨μ₁, hμ₁⟩ : ∃ μ₁ : ℝ, ((μ₁ : ℝ) : EReal) = f x₁ :=
    ⟨(f x₁).toReal, EReal.coe_toReal hx₁ (hf_not_bot x₁)⟩
  have hμ₁lt : ((μ₁ - 1 : ℝ) : EReal) < f x₁ := by
    rw [← hμ₁]
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  obtain ⟨M₀, hM₀⟩ := finite_case f hf_convex hf_lsc ⟨x₁, hx₁⟩ hf_not_bot
    x₁ μ₁ hμ₁.symm (μ₁ - 1) hμ₁lt
  refine ⟨M₀, ?_⟩
  have h2 : ((μ₁ - 1 : ℝ) : EReal) + fenchelConj f M₀
      ≤ ((((M₀ x₁ : ℝ))) : EReal) :=
    EReal.add_le_of_le_sub hM₀
  rw [add_comm] at h2
  have h3 : fenchelConj f M₀
      ≤ ((((M₀ x₁ : ℝ))) : EReal) - ((μ₁ - 1 : ℝ) : EReal) :=
    (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
      (Or.inl ((EReal.coe_lt_top _).ne))).mpr h2
  rw [← EReal.coe_sub] at h3
  exact lt_of_le_of_lt h3 (EReal.coe_lt_top _)

omit [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] in
/-- Per-term bound for a scaled separator plus a finite-conjugate direction. -/
private lemma scale_term_le (f : E → EReal) (hf_not_bot : ∀ x, f x ≠ ⊥)
    (L₀ M₀ : E →L[ℝ] ℝ) (v γ : ℝ)
    (hγ : ((γ : ℝ) : EReal) = fenchelConj f M₀)
    (t : ℝ) (ht : 0 ≤ t)
    (hL₀ : ∀ y ∈ dom f, L₀ y < v)
    (y : E) (hy : y ∈ dom f) :
    (((( (t • L₀ + M₀) y : ℝ))) : EReal) - f y
      ≤ ((((t * v : ℝ))) : EReal) + ((γ : ℝ) : EReal) := by
  have hydom : f y ≠ ⊤ := hy
  have hLt : (t • L₀ + M₀) y = t * L₀ y + M₀ y := rfl
  rw [hLt]
  have hle1 : ((((M₀ y : ℝ))) : EReal) - f y ≤ ((γ : ℝ) : EReal) := by
    rw [hγ]
    unfold fenchelConj
    exact le_iSup (fun z => ((((M₀ z : ℝ))) : EReal) - f z) y
  have hle2 : ((((M₀ y : ℝ))) : EReal) ≤ ((γ : ℝ) : EReal) + f y :=
    (EReal.sub_le_iff_le_add (Or.inl (hf_not_bot y))
      (Or.inl hydom)).mp hle1
  have htv : t * L₀ y ≤ t * v :=
    mul_le_mul_of_nonneg_left (le_of_lt (hL₀ y hy)) ht
  have hmono : ((((t * L₀ y + M₀ y : ℝ))) : EReal)
      ≤ ((((t * v + M₀ y : ℝ))) : EReal) :=
    EReal.coe_le_coe_iff.mpr (add_le_add htv le_rfl)
  have hstep : ((((t * v + M₀ y : ℝ))) : EReal) - f y
      ≤ ((((t * v : ℝ))) : EReal) + ((γ : ℝ) : EReal) := by
    apply EReal.sub_le_of_le_add
    rw [EReal.coe_add]
    calc ((((t * v : ℝ))) : EReal) + ((((M₀ y : ℝ))) : EReal)
        ≤ ((((t * v : ℝ))) : EReal) + (((γ : ℝ) : EReal) + f y) :=
          add_le_add le_rfl hle2
      _ = (((((t * v : ℝ))) : EReal) + ((γ : ℝ) : EReal)) + f y := by
          rw [add_assoc]
  exact le_trans (EReal.sub_le_sub hmono le_rfl) hstep

omit [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] in
/-- The conjugate is never `⊥` when `f` is somewhere finite. -/
private lemma conj_ne_bot (f : E → EReal) (L : E →L[ℝ] ℝ)
    (hf_not_top : ∃ x, f x ≠ ⊤) : fenchelConj f L ≠ ⊥ := by
  obtain ⟨x₁, hx₁⟩ := hf_not_top
  have hterm : ((((L x₁ : ℝ))) : EReal) - f x₁ ≠ ⊥ := by
    rcases eq_or_ne (f x₁) ⊥ with hbot | hbot
    · rw [hbot]
      have h1 : ((((L x₁ : ℝ))) : EReal) - ⊥ = ⊤ := by
        rw [sub_eq_add_neg, EReal.neg_bot]
        exact EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)
      rw [h1]
      exact ne_of_gt bot_lt_top
    · lift f x₁ to ℝ using ⟨hx₁, hbot⟩ with t
      rw [← EReal.coe_sub]
      exact EReal.coe_ne_bot _
  unfold fenchelConj
  have hsup : ((((L x₁ : ℝ))) : EReal) - f x₁
      ≤ ⨆ y : E, ((((L y : ℝ))) : EReal) - f y :=
    le_iSup (fun y => ((((L y : ℝ))) : EReal) - f y) x₁
  intro hcon
  exact hterm (le_antisymm (hcon ▸ hsup) bot_le)

omit [T2Space E] in
/-- Strict separation of a point outside a closed convex set. -/
private lemma separate_point (s : Set E)
    (hs_convex : Convex ℝ s) (hs_closed : IsClosed s)
    (x₀ : E) (hx₀ : x₀ ∉ s) :
    ∃ (L₀ : E →L[ℝ] ℝ) (v : ℝ), v < L₀ x₀ ∧ ∀ a ∈ s, L₀ a < v := by
  obtain ⟨L₀, v, h1, h2⟩ :=
    geometric_hahn_banach_closed_point hs_convex hs_closed hx₀
  exact ⟨L₀, v, h2, h1⟩

omit [T2Space E] in
/-- Outside the domain closure, every real is below the biconjugate. -/
private lemma outside_forall_coe_le (f : E → EReal)
    (hf_convex : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)})
    (hf_lsc : LowerSemicontinuous f)
    (hf_not_top : ∃ x, f x ≠ ⊤)
    (hf_not_bot : ∀ x, f x ≠ ⊥)
    (x₀ : E) (hx₀ : x₀ ∉ closure (dom f)) :
    ∀ R : ℝ, ((R : ℝ) : EReal) ≤ fenchelBiconj f x₀ := by
  obtain ⟨M₀, hM₀⟩ := finite_conj_dir f hf_convex hf_lsc hf_not_top hf_not_bot
  have hclo_convex : Convex ℝ (closure (dom f)) :=
    (convex_dom f hf_convex hf_not_bot).closure
  obtain ⟨L₀, v, hL₀x₀, hL₀clo⟩ :=
    separate_point (closure (dom f)) hclo_convex isClosed_closure x₀ hx₀
  have hCbot : fenchelConj f M₀ ≠ ⊥ := conj_ne_bot f M₀ hf_not_top
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, ((γ : ℝ) : EReal) = fenchelConj f M₀ :=
    ⟨(fenchelConj f M₀).toReal, EReal.coe_toReal (ne_of_lt hM₀) hCbot⟩
  intro R
  set s := L₀ x₀ - v with hs
  have hgap : 0 < s := by linarith [hL₀x₀]
  set X := R - M₀ x₀ + γ with hX
  set t := max 0 (X / s) with ht
  have ht0 : 0 ≤ t := le_max_left 0 _
  have hts : X ≤ t * s := (div_le_iff₀ hgap).mp (le_max_right 0 _)
  set Lt : E →L[ℝ] ℝ := t • L₀ + M₀ with hLt
  have hL₀dom : ∀ y ∈ dom f, L₀ y < v :=
    fun y hy => hL₀clo y (subset_closure hy)
  have hsup : fenchelConj f Lt
      ≤ ((((t * v : ℝ))) : EReal) + ((γ : ℝ) : EReal) := by
    unfold fenchelConj
    apply ciSup_le
    intro y
    rcases eq_or_ne (f y) ⊤ with hy | hy
    · rw [hy, EReal.sub_top]
      exact bot_le
    · exact scale_term_le f hf_not_bot L₀ M₀ v γ hγ t ht0 hL₀dom y hy
  have hterm : ((((Lt x₀ : ℝ))) : EReal) - fenchelConj f Lt
      ≤ fenchelBiconj f x₀ := by
    unfold fenchelBiconj
    exact le_iSup (fun L => ((((L x₀ : ℝ))) : EReal) - fenchelConj f L) Lt
  have hsub : ((((Lt x₀ : ℝ))) : EReal)
        - (((((t * v : ℝ))) : EReal) + ((γ : ℝ) : EReal))
      ≤ ((((Lt x₀ : ℝ))) : EReal) - fenchelConj f Lt :=
    EReal.sub_le_sub le_rfl hsup
  have hLtx₀ : Lt x₀ = t * L₀ x₀ + M₀ x₀ := rfl
  have hval : ((((Lt x₀ : ℝ))) : EReal)
        - (((((t * v : ℝ))) : EReal) + ((γ : ℝ) : EReal))
      = ((((t * s + M₀ x₀ - γ : ℝ))) : EReal) := by
    rw [hLtx₀, ← EReal.coe_add, ← EReal.coe_sub]
    congr 1
    rw [hs]
    ring
  have hRle : ((R : ℝ) : EReal) ≤ ((((t * s + M₀ x₀ - γ : ℝ))) : EReal) :=
    EReal.coe_le_coe_iff.mpr (by linarith [hts])
  calc ((R : ℝ) : EReal) ≤ ((((t * s + M₀ x₀ - γ : ℝ))) : EReal) := hRle
    _ = ((((Lt x₀ : ℝ))) : EReal)
          - (((((t * v : ℝ))) : EReal) + ((γ : ℝ) : EReal)) := hval.symm
    _ ≤ ((((Lt x₀ : ℝ))) : EReal) - fenchelConj f Lt := hsub
    _ ≤ fenchelBiconj f x₀ := hterm

omit [T2Space E] in
/-- Finite values are below the biconjugate, by real density. -/
private lemma finite_le (f : E → EReal)
    (hf_convex : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)})
    (hf_lsc : LowerSemicontinuous f)
    (hf_not_top : ∃ x, f x ≠ ⊤)
    (hf_not_bot : ∀ x, f x ≠ ⊥)
    (x₀ : E) (μ₀ : ℝ) (hμ₀ : f x₀ = (μ₀ : EReal)) :
    f x₀ ≤ fenchelBiconj f x₀ := by
  have h : ∀ a : ℝ, (a : EReal) < f x₀ → (a : EReal) ≤ fenchelBiconj f x₀ := by
    intro a ha
    obtain ⟨L', hL'⟩ := finite_case f hf_convex hf_lsc hf_not_top hf_not_bot
      x₀ μ₀ hμ₀ a ha
    calc (a : EReal)
        ≤ ((((L' x₀ : ℝ))) : EReal) - fenchelConj f L' := hL'
      _ ≤ fenchelBiconj f x₀ := by
          unfold fenchelBiconj
          exact le_iSup (fun L => ((((L x₀ : ℝ))) : EReal) - fenchelConj f L) L'
  rw [hμ₀]
  by_contra hcon
  have hlt : fenchelBiconj f x₀ < (μ₀ : EReal) := lt_of_not_ge hcon
  by_cases hbot : fenchelBiconj f x₀ = ⊥
  · have h2 := h (μ₀ - 1) (by
      rw [hμ₀]
      exact EReal.coe_lt_coe_iff.mpr (by linarith))
    rw [hbot] at h2
    exact EReal.coe_ne_bot _ (le_bot_iff.mp h2)
  · have hne_top : fenchelBiconj f x₀ ≠ ⊤ := fun heq => by
      rw [heq] at hlt
      exact absurd hlt not_top_lt
    obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, ((σ : ℝ) : EReal) = fenchelBiconj f x₀ :=
      ⟨_, EReal.coe_toReal hne_top hbot⟩
    have hσμ : σ < μ₀ := by
      have h := hlt
      rw [← hσ] at h
      exact EReal.coe_lt_coe_iff.mp h
    set a : ℝ := (σ + μ₀) / 2 with hadef
    have hσa : σ < a := by rw [hadef]; linarith [hσμ]
    have haμ : a < μ₀ := by rw [hadef]; linarith [hσμ]
    have h2 := h a (by
      rw [hμ₀]
      exact EReal.coe_lt_coe_iff.mpr haμ)
    rw [← hσ] at h2
    have h3 : ((σ : ℝ) : EReal) < (a : EReal) :=
      EReal.coe_lt_coe_iff.mpr hσa
    exact lt_irrefl _ (lt_of_le_of_lt h2 h3)

omit [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] in
/-- Density bridge: reals below the biconjugate force `⊤` below it. -/
private lemma le_of_forall_coe_le (f : E → EReal) (x₀ : E)
    (h : ∀ a : ℝ, ((a : ℝ) : EReal) ≤ fenchelBiconj f x₀)
    (hfx : f x₀ = ⊤) : f x₀ ≤ fenchelBiconj f x₀ := by
  rw [hfx]
  by_contra hcon
  have hlt : fenchelBiconj f x₀ < ⊤ := lt_of_not_ge hcon
  have hne : fenchelBiconj f x₀ ≠ ⊤ := ne_of_lt hlt
  rcases eq_or_ne (fenchelBiconj f x₀) ⊥ with hb | hb
  · have h1 := h 0
    rw [hb] at h1
    exact EReal.coe_ne_bot 0 (le_antisymm h1 bot_le)
  · obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, ((σ : ℝ) : EReal) = fenchelBiconj f x₀ :=
      ⟨_, EReal.coe_toReal hne hb⟩
    have h2 := h (σ + 1)
    rw [← hσ] at h2
    have hle := EReal.coe_le_coe_iff.mp h2
    linarith

omit [T2Space E] in
/-- Hard direction at a point: `f x₀ ≤ f** x₀` by the three cases. -/
private lemma le_fenchelBiconj (f : E → EReal)
    (hf_convex : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)})
    (hf_lsc : LowerSemicontinuous f)
    (hf_not_top : ∃ x, f x ≠ ⊤)
    (hf_not_bot : ∀ x, f x ≠ ⊥)
    (x₀ : E) : f x₀ ≤ fenchelBiconj f x₀ := by
  by_cases hfx : f x₀ = ⊤
  · by_cases hx₀ : x₀ ∈ closure (dom f)
    · have h : ∀ a : ℝ, ((a : ℝ) : EReal) ≤ fenchelBiconj f x₀ := by
        intro a
        obtain ⟨L', hL'⟩ := closure_case f hf_convex hf_lsc hf_not_top
          hf_not_bot x₀ hfx hx₀ a
        calc ((a : ℝ) : EReal)
            ≤ ((((L' x₀ : ℝ))) : EReal) - fenchelConj f L' := hL'
          _ ≤ fenchelBiconj f x₀ := by
              unfold fenchelBiconj
              exact le_iSup
                (fun L => ((((L x₀ : ℝ))) : EReal) - fenchelConj f L) L'
      exact le_of_forall_coe_le f x₀ h hfx
    · exact le_of_forall_coe_le f x₀
        (outside_forall_coe_le f hf_convex hf_lsc hf_not_top hf_not_bot x₀ hx₀)
        hfx
  · obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀ : ℝ, f x₀ = (μ₀ : EReal) :=
      ⟨(f x₀).toReal, (EReal.coe_toReal hfx (hf_not_bot x₀)).symm⟩
    exact finite_le f hf_convex hf_lsc hf_not_top hf_not_bot x₀ μ₀ hμ₀

omit [T2Space E] in
/-- Fenchel–Moreau at a point: `f x₀ = f** x₀`. -/
private lemma fenchel_moreau_pt (f : E → EReal)
    (hf_convex : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)})
    (hf_lsc : LowerSemicontinuous f)
    (hf_not_top : ∃ x, f x ≠ ⊤)
    (hf_not_bot : ∀ x, f x ≠ ⊥)
    (x₀ : E) : f x₀ = fenchelBiconj f x₀ :=
  le_antisymm
    (le_fenchelBiconj f hf_convex hf_lsc hf_not_top hf_not_bot x₀)
    (biconj_le f hf_not_bot x₀)

omit [T2Space E] in
/-- **Fenchel–Moreau theorem.** Let $E$ be a locally convex real topological vector space, not
necessarily Hausdorff. Let $f : E \to [-\infty, \infty]$ be lower semicontinuous, never equal to
$-\infty$, not identically $+\infty$, and convex in the sense that the set
$\{(x, r) \in E \times \mathbb{R} : f(x) \le r\}$ is convex. Then for every $x \in E$,
$f(x) = \sup_L \big(L(x) - \sup_{y \in E} (L(y) - f(y))\big)$, where $L$ ranges over the
continuous linear functionals $E \to \mathbb{R}$; that is, $f$ equals its Fenchel biconjugate.

Source: Werner Fenchel, *Convex Cones, Sets, and Functions: From Notes
by D. W. Blackett of Lectures at Princeton University, 1951*, Princeton
University Department of Mathematics, 1953, Open Library OL1430688W; and
Jean-Jacques Moreau, "Fonctions convexes duales et points proximaux,"
C. R. Acad. Sci. Paris 255 (1962), 2897–2899, zbMATH 0118.10502. -/
theorem fenchel_moreau
    {f : E → EReal}
    (hf_convex : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)})
    (hf_lsc : LowerSemicontinuous f)
    (hf_not_top : ∃ x, f x ≠ ⊤)
    (hf_not_bot : ∀ x, f x ≠ ⊥) :
    ∀ x : E,
      f x = ⨆ (L : E →L[ℝ] ℝ),
        (((L x : ℝ) : EReal) - (⨆ y : E, ((L y : ℝ) : EReal) - f y)) := by
  intro x
  exact fenchel_moreau_pt f hf_convex hf_lsc hf_not_top hf_not_bot x

end MathlibExt.Analysis.Convex.FenchelMoreau
