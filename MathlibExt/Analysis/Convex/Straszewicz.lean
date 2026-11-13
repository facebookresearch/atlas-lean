/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Tactic.Module
public import Mathlib.Topology.Bases

@[expose] public section

namespace MathlibExt.Analysis.Convex.Straszewicz

/-!
# Straszewicz's theorem on exposed points

Every extreme point of a compact convex set in a finite-dimensional real
normed space lies in the closure of its exposed points.

Primary source: S. Straszewicz, "Über exponierte Punkte abgeschlossener
Punktmengen", Fundamenta Mathematicae 24 (1935), 139–143,
DOI 10.4064/FM-24-1-139-143.
-/

open Set Metric Filter TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Convex hull of a compact set is compact.** Let $E$ be a finite-dimensional real normed
space. If $K \subseteq E$ is compact, then the convex hull of $K$ is compact. -/
theorem IsCompact.convexHull_of_compact {K : Set E} (hK : IsCompact K) :
    IsCompact (convexHull ℝ K) := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · rw [convexHull_empty]
    exact isCompact_empty
  · set d := Module.finrank ℝ E with hd
    have himg : convexHull ℝ K =
        (fun p : Convexity.StdSimplex ℝ (Fin (d + 1)) × (Fin (d + 1) → E) =>
          ∑ i, p.1.weights i • p.2 i) ''
          (Set.univ ×ˢ {z : Fin (d + 1) → E | ∀ i, z i ∈ K}) := by
      apply Subset.antisymm
      · intro x hx
        rw [convexHull_eq_union] at hx
        simp only [Set.mem_iUnion, exists_prop] at hx
        obtain ⟨t, htK, htind, hxt⟩ := hx
        rw [Finset.convexHull_eq] at hxt
        obtain ⟨w, hw0, hw1, hcm⟩ := hxt
        have hxsum : x = ∑ y ∈ t, w y • y := by
          rw [← hcm, Finset.centerMass_eq_of_sum_1 t id hw1]
          simp only [id_eq]
        have hcard : t.card ≤ d + 1 := by
          have h1 := AffineIndependent.card_le_finrank_succ htind
          have hle := Submodule.finrank_le
            (vectorSpan ℝ (Set.range ((↑) : ↥t → E)))
          have hc : Fintype.card ↥t = t.card := Fintype.card_coe t
          omega
        classical
        have htne : t.Nonempty := by
          by_contra h
          rw [Finset.not_nonempty_iff_eq_empty] at h
          simp [h] at hw1
        have : Nonempty ↥t := (Finset.coe_nonempty.mpr htne).to_subtype
        let emb : ↥t ↪ Fin (d + 1) :=
          { toFun := fun i => Fin.castLE hcard (t.equivFin i)
            inj' := fun a b hab => t.equivFin.injective (Fin.ext (by
              have h2 := congrArg Fin.val hab
              simpa using h2)) }
        set r := Finset.univ.map emb with hr
        set w'' : Fin (d + 1) → ℝ := fun j =>
          if _ : j ∈ r then w ↑(Function.invFun (⇑emb) j) else 0 with hw''
        set z'' : Fin (d + 1) → E := fun j =>
          if h : j ∈ r then (↑(Function.invFun (⇑emb) j : ↥t) : E) else p₀ with hz''
        have hw''0 : ∀ j, 0 ≤ w'' j := by
          intro j
          by_cases hj : j ∈ r
          · simp only [hw'']
            rw [dite_eq_left hj]
            exact hw0 _ (Finset.mem_coe.mp (Function.invFun (⇑emb) j).2)
          · simp only [hw'']
            rw [dite_eq_right hj]
        have hw''1 : ∑ j, w'' j = 1 := by
          have hcongrw : ∀ i : ↥t,
              w ↑(Function.invFun (⇑emb) (emb i)) = w ↑i := fun i =>
            congrArg w
              (congrArg Subtype.val (Function.leftInverse_invFun emb.injective i))
          have e1 : ∑ j, w'' j = ∑ j ∈ r, w ↑(Function.invFun (⇑emb) j) := by
            rw [← Finset.sum_subset (Finset.subset_univ r) (fun j _ hjr => by
              simp only [hw'']
              rw [dite_eq_right hjr])]
            refine Finset.sum_congr rfl (fun j hj => ?_)
            simp only [hw'']
            rw [dite_eq_left hj]
          have e2 : (∑ i ∈ (Finset.univ : Finset ↥t), w (i : E)) =
              ∑ y ∈ t, w y := by
            apply Finset.sum_bij (fun (i : ↥t) (_ : i ∈ (Finset.univ : Finset ↥t)) => (i : E))
            · intro i _
              exact Finset.mem_coe.mp i.2
            · intro i _ j _ h
              exact Subtype.ext h
            · intro y hy
              exact ⟨⟨y, Finset.mem_coe.mpr hy⟩, Finset.mem_univ _, rfl⟩
            · intro i _
              rfl
          rw [e1, hr, Finset.sum_map,
            Finset.sum_congr rfl (fun (x : ↥t) _ => hcongrw x), e2, hw1]
        let w' : Convexity.StdSimplex ℝ (Fin (d + 1)) :=
          { weights := Finsupp.equivFunOnFinite.symm w'',
            nonneg := by
              intro j
              simpa using hw''0 j
            total := by
              simpa [Finsupp.sum_fintype] using hw''1 }
        have hw'eq : ∀ j, w'.weights j = w'' j := fun j => rfl
        have hmem : (w', z'') ∈
            Set.univ ×ˢ {z : Fin (d + 1) → E | ∀ i, z i ∈ K} := by
          constructor
          · trivial
          · intro j
            by_cases hj : j ∈ r
            · simp only [hz'']
              rw [dite_eq_left hj]
              exact htK (Function.invFun (⇑emb) j).2
            · simp only [hz'']
              rw [dite_eq_right hj]
              exact hp₀
        refine ⟨(w', z''), hmem, ?_⟩
        change (∑ j, w'.weights j • z'' j) = x
        have e3 : (∑ j, w'.weights j • z'' j) = ∑ y ∈ t, w y • y := by
          have f1 : ∑ j, w'.weights j • z'' j
              = ∑ j ∈ r, w ↑(Function.invFun (⇑emb) j) •
                (↑(Function.invFun (⇑emb) j : ↥t) : E) := by
            rw [← Finset.sum_subset (Finset.subset_univ r) (fun j _ hjr => by
              rw [hw'eq j]
              simp only [hw'', hz'']
              rw [dite_eq_right hjr, dite_eq_right hjr, zero_smul])]
            refine Finset.sum_congr rfl (fun j hj => ?_)
            rw [hw'eq j]
            simp only [hw'', hz'']
            rw [dite_eq_left hj, dite_eq_left hj]
          have e4 : (∑ i ∈ (Finset.univ : Finset ↥t), w (i : E) • (i : E)) =
              ∑ y ∈ t, w y • y := by
            apply Finset.sum_bij (fun (i : ↥t) (_ : i ∈ (Finset.univ : Finset ↥t)) => (i : E))
            · intro i _
              exact Finset.mem_coe.mp i.2
            · intro i _ j _ h
              exact Subtype.ext h
            · intro y hy
              exact ⟨⟨y, Finset.mem_coe.mpr hy⟩, Finset.mem_univ _, rfl⟩
            · intro i _
              rfl
          have hcongrwz : ∀ i : ↥t, w ↑(Function.invFun (⇑emb) (emb i)) •
              (↑(Function.invFun (⇑emb) (emb i) : ↥t) : E) = w ↑i • ↑i := fun i => by
            rw [Function.leftInverse_invFun emb.injective i]
          rw [f1, hr, Finset.sum_map,
            Finset.sum_congr rfl (fun (x : ↥t) _ => hcongrwz x), e4]
        rw [e3, hxsum]
      · intro x hx
        obtain ⟨⟨w, z⟩, ⟨-, hzS⟩, rfl⟩ := hx
        exact Convex.sum_mem (convex_convexHull ℝ K) (t := Finset.univ)
          (fun i _ => w.nonneg i) (by simp)
          (fun i _ => subset_convexHull ℝ K (hzS i))
    have hdom : IsCompact
        ((Set.univ : Set (Convexity.StdSimplex ℝ (Fin (d + 1)))) ×ˢ
          {z : Fin (d + 1) → E | ∀ i, z i ∈ K}) :=
      isCompact_univ.prod (isCompact_pi_infinite (fun _ => hK))
    have hcont : Continuous
        (fun p : Convexity.StdSimplex ℝ (Fin (d + 1)) × (Fin (d + 1) → E) =>
          ∑ i, p.1.weights i • p.2 i) :=
      continuous_finsetSum _ fun i _ =>
        Continuous.smul
          ((Convexity.StdSimplex.continuous_weights_apply ℝ i).comp continuous_fst)
          ((continuous_apply i).comp continuous_snd)
    rw [himg]
    exact hdom.image hcont

/-- **Difference quotients.** Let $E$ be a real normed space and $E^*$ its continuous dual. For
$h : E^* \to \mathbb{R}$ and $x, v \in E^*$, the difference quotients of $h$ at $x$ in direction
$v$ form the set $\{(h(x + t v) - h(x))/t : t > 0\}$.

When $h$ is convex this set is bounded below, and its infimum is the one-sided directional
derivative of $h$ at $x$ in direction $v$. -/
noncomputable def dirQuot (h : StrongDual ℝ E → ℝ) (x v : StrongDual ℝ E) : Set ℝ :=
  (fun t : ℝ => (h (x + t • v) - h x) / t) '' Ioi 0

/-- **Directional derivative.** Let $E$ be a real normed space with continuous dual $E^*$. For
$h : E^* \to \mathbb{R}$ and $x, v \in E^*$, the directional derivative of $h$ at $x$ in
direction $v$ is the infimum of the difference quotients,
$h'(x; v) = \inf_{t > 0} \frac{h(x + t v) - h(x)}{t}$, which is taken to be $0$ when these
quotients are not bounded below.

For convex $h$ the quotients are bounded below, so this is the usual one-sided directional
derivative. -/
noncomputable def dirDeriv (h : StrongDual ℝ E → ℝ) (x v : StrongDual ℝ E) : ℝ :=
  sInf (dirQuot h x v)

variable {h : StrongDual ℝ E → ℝ} {x : StrongDual ℝ E}

omit [FiniteDimensional ℝ E] in
/-- **Restriction of a convex function to a line.** Let $E$ be a real normed space with
continuous dual $E^*$, and let $h : E^* \to \mathbb{R}$ be convex. For all $x, v \in E^*$, the
function $s \mapsto h(x + s v)$ is convex on $\mathbb{R}$. -/
theorem convexOn_line (hconv : ConvexOn ℝ univ h) (v : StrongDual ℝ E) :
    ConvexOn ℝ univ (fun s : ℝ => h (x + s • v)) := by
  refine ⟨convex_univ, fun s _ u _ a b ha hb hab => ?_⟩
  have key : x + (a * s + b * u) • v = a • (x + s • v) + b • (x + u • v) := by
    have e1 : (a * s + b * u) • v = a • (s • v) + b • (u • v) := by
      rw [add_smul, mul_smul, mul_smul]
    have e2 : a • x + b • x = x := by rw [← add_smul, hab, one_smul]
    calc x + (a * s + b * u) • v
        = (a • x + b • x) + (a • (s • v) + b • (u • v)) := by rw [e1, e2]
      _ = a • (x + s • v) + b • (x + u • v) := by
          rw [smul_add, smul_add]
          abel
  simp only [smul_eq_mul] at key ⊢
  rw [key]
  exact hconv.2 (mem_univ _) (mem_univ _) ha hb hab

omit [FiniteDimensional ℝ E] in
/-- **Difference quotients of a convex function are bounded below.** Let $E$ be a real normed
space, $E^*$ its continuous dual, and $h : E^* \to \mathbb{R}$ a convex function. For all
$x, v \in E^*$, the set of difference quotients $\{(h(x + t v) - h(x))/t : t > 0\}$ is bounded
below.

The bound comes from comparing slopes of $h$ on the line through $x$ in direction $v$. -/
theorem dirQuot_bddBelow (hconv : ConvexOn ℝ univ h) (v : StrongDual ℝ E) :
    BddBelow (dirQuot h x v) := by
  refine ⟨h x - h (x - v), fun z hz => ?_⟩
  obtain ⟨t, ht, rfl⟩ := hz
  change h x - h (x - v) ≤ (h (x + t • v) - h x) / t
  have hψ := convexOn_line (x := x) hconv v
  have hsl := ConvexOn.slope_mono_adjacent hψ (mem_univ (-1)) (mem_univ t)
    (by norm_num : (-1 : ℝ) < 0) ht
  have e0' : h (x + (0 : ℝ) • v) = h x := by simp
  have em1 : h (x + (-1 : ℝ) • v) = h (x - v) := by
    rw [neg_one_smul ℝ v, sub_eq_add_neg]
  have h1 : h x - h (x - v)
      = (h (x + (0 : ℝ) • v) - h (x + (-1 : ℝ) • v)) / ((0 : ℝ) - -1) := by
    rw [e0', em1]
    norm_num
  have h2 : (h (x + t • v) - h x) / t
      = (h (x + t • v) - h (x + (0 : ℝ) • v)) / (t - 0) := by
    rw [e0']
    norm_num
  rw [h1, h2]
  exact hsl

omit [FiniteDimensional ℝ E] in
theorem dirQuot_nonempty (v : StrongDual ℝ E) : (dirQuot h x v).Nonempty :=
  Set.image_nonempty.mpr nonempty_Ioi

omit [FiniteDimensional ℝ E] in
theorem dirDeriv_le_quot (hconv : ConvexOn ℝ univ h) (v : StrongDual ℝ E)
    {t : ℝ} (ht : 0 < t) : dirDeriv h x v ≤ (h (x + t • v) - h x) / t :=
  csInf_le (dirQuot_bddBelow hconv v) ⟨t, ht, rfl⟩

omit [FiniteDimensional ℝ E] in
/-- **Subadditivity of the directional derivative.** Let $E$ be a real normed space with
continuous dual $E^*$, let $h : E^* \to \mathbb{R}$ be convex, and write $h'(x; v)$ for the
directional derivative of $h$ at $x$ in direction $v$. For all $x, v, w \in E^*$,
$h'(x; v + w) \le h'(x; v) + h'(x; w)$. -/
theorem dirDeriv_subadd (hconv : ConvexOn ℝ univ h) (v w : StrongDual ℝ E) :
    dirDeriv h x (v + w) ≤ dirDeriv h x v + dirDeriv h x w := by
  have key : ∀ s₁ s₂ : ℝ, 0 < s₁ → 0 < s₂ → dirDeriv h x (v + w)
      ≤ (h (x + s₁ • v) - h x) / s₁ + ((h (x + s₂ • w) - h x) / s₂) := by
    intro s₁ s₂ hs₁ hs₂
    set t := s₁ * s₂ / (s₁ + s₂) with ht
    have htpos : 0 < t := by
      rw [ht]
      positivity
    have hs₁' : s₁ ≠ 0 := ne_of_gt hs₁
    have hs₂' : s₂ ≠ 0 := ne_of_gt hs₂
    have hsum' : s₁ + s₂ ≠ 0 := ne_of_gt (add_pos hs₁ hs₂)
    have hlam : t / s₁ + t / s₂ = 1 := by
      rw [ht]
      field_simp
      ring
    have c1 : (t / s₁) * s₁ = t := div_mul_cancel₀ _ hs₁'
    have c2 : (t / s₂) * s₂ = t := div_mul_cancel₀ _ hs₂'
    have hdecomp : x + t • (v + w)
        = (t / s₁) • (x + s₁ • v) + (t / s₂) • (x + s₂ • w) := by
      have r1 : (t / s₁) • (s₁ • v) = t • v := by rw [← mul_smul, c1]
      have r2 : (t / s₂) • (s₂ • w) = t • w := by rw [← mul_smul, c2]
      have rx : (t / s₁) • x + (t / s₂) • x = x := by
        rw [← add_smul, hlam, one_smul]
      calc x + t • (v + w) = x + (t • v + t • w) := by rw [smul_add]
        _ = ((t / s₁) • x + (t / s₂) • x) + (t • v + t • w) := by rw [rx]
        _ = (t / s₁) • (x + s₁ • v) + (t / s₂) • (x + s₂ • w) := by
            rw [smul_add, smul_add, r1, r2]
            abel
    have hcvx := hconv.2 (mem_univ (x + s₁ • v)) (mem_univ (x + s₂ • w))
      (div_nonneg htpos.le hs₁.le) (div_nonneg htpos.le hs₂.le) hlam
    rw [← hdecomp] at hcvx
    have hQt : dirDeriv h x (v + w) ≤ (h (x + t • (v + w)) - h x) / t :=
      dirDeriv_le_quot hconv _ htpos
    have alg : ((t / s₁) * h (x + s₁ • v) + (t / s₂) * h (x + s₂ • w) - h x) / t
        = (h (x + s₁ • v) - h x) / s₁ + ((h (x + s₂ • w) - h x) / s₂) := by
      have ht' : t ≠ 0 := ne_of_gt htpos
      rw [ht]
      field_simp
      ring
    calc dirDeriv h x (v + w)
        ≤ (h (x + t • (v + w)) - h x) / t := hQt
      _ ≤ ((t / s₁) * h (x + s₁ • v) + (t / s₂) * h (x + s₂ • w) - h x) / t := by
          rw [div_le_div_iff_of_pos_right htpos]
          have hcvx' := hcvx
          simp only [smul_eq_mul] at hcvx'
          linarith
      _ = _ := alg
  have step1 : ∀ s₂ : ℝ, 0 < s₂ → dirDeriv h x (v + w)
      ≤ dirDeriv h x v + (h (x + s₂ • w) - h x) / s₂ := by
    intro s₂ hs₂
    have hle : dirDeriv h x (v + w) - (h (x + s₂ • w) - h x) / s₂
        ≤ dirDeriv h x v := by
      apply le_csInf (dirQuot_nonempty (h := h) (x := x) v)
      intro b hb
      obtain ⟨s₁, hs₁, rfl⟩ := hb
      change dirDeriv h x (v + w) - (h (x + s₂ • w) - h x) / s₂
        ≤ (h (x + s₁ • v) - h x) / s₁
      have := key s₁ s₂ hs₁ hs₂
      linarith
    linarith
  have hle : dirDeriv h x (v + w) - dirDeriv h x v ≤ dirDeriv h x w := by
    apply le_csInf (dirQuot_nonempty (h := h) (x := x) w)
    intro b hb
    obtain ⟨s₂, hs₂, rfl⟩ := hb
    change dirDeriv h x (v + w) - dirDeriv h x v ≤ (h (x + s₂ • w) - h x) / s₂
    have := step1 s₂ hs₂
    linarith
  linarith

omit [FiniteDimensional ℝ E] in
/-- **Directional derivative in direction zero.** Let $E$ be a real normed space with continuous
dual $E^*$ and let $h : E^* \to \mathbb{R}$ be any function. For every $x \in E^*$, the directional
derivative of $h$ at $x$ in direction $0$ is $0$. -/
theorem dirDeriv_zero : dirDeriv h x 0 = 0 := by
  have hset : dirQuot h x 0 = {0} := by
    ext z
    simp only [dirQuot, Set.mem_image, Set.mem_Ioi, Set.mem_singleton_iff]
    constructor
    · rintro ⟨t, ht, rfl⟩
      simp [smul_zero, add_zero, sub_self]
    · intro hz
      refine ⟨1, one_pos, ?_⟩
      simp [hz, smul_zero, add_zero, sub_self]
  have hle : sInf ({0} : Set ℝ) ≤ 0 :=
    csInf_le ⟨0, fun b hb => by rw [Set.mem_singleton_iff.mp hb]⟩
      ((Set.mem_singleton_iff).mpr rfl)
  have hge : (0 : ℝ) ≤ sInf ({0} : Set ℝ) :=
    le_csInf ⟨0, (Set.mem_singleton_iff).mpr rfl⟩
      (fun b hb => by rw [Set.mem_singleton_iff.mp hb])
  rw [dirDeriv, hset]
  exact le_antisymm hle hge

omit [FiniteDimensional ℝ E] in
/-- **Opposite directional derivatives have nonnegative sum.** Let $E$ be a real normed space
with continuous dual $E^*$, let $h : E^* \to \mathbb{R}$ be convex, and write $h'(x; v)$ for the
directional derivative of $h$ at $x$ in direction $v$. For all $x, v \in E^*$,
$h'(x; v) + h'(x; -v) \ge 0$. -/
theorem dirDeriv_add_neg_nonneg (hconv : ConvexOn ℝ univ h) (v : StrongDual ℝ E) :
    0 ≤ dirDeriv h x v + dirDeriv h x (-v) := by
  have hsub := dirDeriv_subadd (x := x) hconv v (-v)
  have h0 := dirDeriv_zero (h := h) (x := x)
  rw [add_neg_cancel] at hsub
  rw [h0] at hsub
  exact hsub

section Support

variable {K : Set E}

/-- **Support function.** For a set $K$ in a real normed space $E$, the support function of $K$
sends a continuous linear functional $\ell$ on $E$ to the supremum $\sup_{x \in K} \ell(x)$ of the
values of $\ell$ on $K$.

The supremum is taken in $\mathbb{R}$, so it is $0$ when $K$ is empty or $\ell$ is unbounded
above on $K$; for nonempty compact $K$ it is attained. -/
noncomputable def suppFunc (K : Set E) : StrongDual ℝ E → ℝ :=
  fun l => sSup ((fun x => l x) '' K)

omit [FiniteDimensional ℝ E] in
/-- **The support function of a compact set is attained.** Let $K$ be a nonempty compact subset
of a real normed space $E$, and let $h_K(l) = \sup_{x \in K} l(x)$ be its support function on the
continuous dual $E^*$. For every $l \in E^*$ there is $x \in K$ with $l(x) = h_K(l)$. -/
theorem suppFunc_attain (hK : IsCompact K) (hKne : K.Nonempty) (l : StrongDual ℝ E) :
    ∃ x ∈ K, l x = suppFunc K l := by
  have hcont : Continuous (fun x => l x) := (l : E →L[ℝ] ℝ).continuous
  have himg : IsCompact ((fun x => l x) '' K) := hK.image hcont
  have hne : ((fun x => l x) '' K).Nonempty := Set.image_nonempty.mpr hKne
  obtain ⟨x, hxK, hxl⟩ := IsCompact.sSup_mem himg hne
  exact ⟨x, hxK, hxl⟩

omit [FiniteDimensional ℝ E] in
/-- **The support function of a compact set is convex.** Let $K$ be a nonempty compact subset of
a real normed space $E$. Its support function $h_K(l) = \sup_{x \in K} l(x)$ is a convex function
on the whole continuous dual $E^*$. -/
theorem suppFunc_convex (hK : IsCompact K) (hKne : K.Nonempty) :
    ConvexOn ℝ univ (suppFunc K) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hcont : ∀ l : StrongDual ℝ E, Continuous (fun x => l x) := fun l =>
    (l : E →L[ℝ] ℝ).continuous
  have hbdd : ∀ l : StrongDual ℝ E, BddAbove ((fun x => l x) '' K) := fun l =>
    (hK.image (hcont l)).bddAbove
  apply csSup_le (Set.image_nonempty.mpr hKne)
  rintro z ⟨w, hwK, rfl⟩
  change (a • x + b • y) w ≤ a • suppFunc K x + b • suppFunc K y
  have hxw : x w ≤ suppFunc K x := le_csSup (hbdd x) ⟨w, hwK, rfl⟩
  have hyw : y w ≤ suppFunc K y := le_csSup (hbdd y) ⟨w, hwK, rfl⟩
  have e : (a • x + b • y) w = a * x w + b * y w := by
    simp [add_apply, smul_apply, smul_eq_mul]
  have hle : a * x w + b * y w ≤ a * suppFunc K x + b * suppFunc K y :=
    add_le_add (mul_le_mul_of_nonneg_left hxw ha) (mul_le_mul_of_nonneg_left hyw hb)
  rw [e]
  simp only [smul_eq_mul]
  exact hle

omit [FiniteDimensional ℝ E] in
/-- **The support function of a compact set is Lipschitz.** Let $K$ be a nonempty compact subset
of a real normed space $E$, and let $h_K(l) = \sup_{x \in K} l(x)$ be its support function on the
continuous dual $E^*$. There is a constant $C \ge 0$ such that
$h_K(l_1) - h_K(l_2) \le C \|l_1 - l_2\|$ for all $l_1, l_2 \in E^*$, where $\|\cdot\|$ is the
operator norm. -/
theorem suppFunc_lipschitz (hK : IsCompact K) (hKne : K.Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ l₁ l₂ : StrongDual ℝ E,
      suppFunc K l₁ - suppFunc K l₂ ≤ C * ‖l₁ - l₂‖ := by
  obtain ⟨xB, hxBK, hBmax⟩ := hK.exists_isMaxOn hKne continuous_norm.continuousOn
  refine ⟨‖xB‖, norm_nonneg _, fun l₁ l₂ => ?_⟩
  obtain ⟨x₁, hx₁K, hx₁e⟩ := suppFunc_attain hK hKne l₁
  have hle1 : l₁ x₁ - l₂ x₁ ≤ ‖l₁ - l₂‖ * ‖xB‖ := by
    have e : l₁ x₁ - l₂ x₁ = (l₁ - l₂) x₁ := by rw [sub_apply]
    rw [e]
    calc (l₁ - l₂) x₁ ≤ ‖(l₁ - l₂) x₁‖ := le_abs_self _
      _ ≤ ‖l₁ - l₂‖ * ‖x₁‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖l₁ - l₂‖ * ‖xB‖ :=
          mul_le_mul_of_nonneg_left (hBmax hx₁K) (norm_nonneg _)
  have hle2 : l₂ x₁ ≤ suppFunc K l₂ :=
    le_csSup ((hK.image
      (show Continuous (fun x => l₂ x) from (l₂ : E →L[ℝ] ℝ).continuous))).bddAbove
      ⟨x₁, hx₁K, rfl⟩
  rw [← hx₁e]
  linarith

omit [FiniteDimensional ℝ E] in
/-- **The support function of a compact set is continuous.** Let $K$ be a nonempty compact
subset of a real normed space $E$. Its support function $h_K(l) = \sup_{x \in K} l(x)$ is
continuous on the continuous dual $E^*$ with the operator norm. -/
theorem suppFunc_continuous (hK : IsCompact K) (hKne : K.Nonempty) :
    Continuous (suppFunc K) := by
  obtain ⟨C, hC, hlip⟩ := suppFunc_lipschitz hK hKne
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  have hCε : ∀ ε : ℝ, 0 < ε → C * (ε / (C + 1)) ≤ ε := by
    intro ε hε
    rw [← mul_div_assoc, div_le_iff₀ hC1, mul_add, mul_one]
    linarith [mul_nonneg hC hε.le]
  rw [Metric.continuous_iff]
  intro l₀ ε hε
  refine ⟨ε / (C + 1), div_pos hε hC1, fun l hl => ?_⟩
  rw [dist_eq_norm] at hl
  have hmain : C * ‖l - l₀‖ < ε := by
    by_cases hC0 : C = 0
    · rw [hC0, zero_mul]
      exact hε
    · have hCpos : 0 < C := lt_of_le_of_ne' hC hC0
      calc C * ‖l - l₀‖ < C * (ε / (C + 1)) :=
              mul_lt_mul_of_pos_left hl hCpos
        _ ≤ ε := hCε ε hε
  have h1 := hlip l l₀
  have h2 := hlip l₀ l
  have hn : ‖l₀ - l‖ = ‖l - l₀‖ := by rw [← norm_neg, neg_sub]
  rw [dist_eq_norm, Real.norm_eq_abs, abs_lt]
  constructor
  · have h2' : suppFunc K l₀ - suppFunc K l ≤ C * ‖l - l₀‖ := by
      calc suppFunc K l₀ - suppFunc K l ≤ C * ‖l₀ - l‖ := h2
        _ = C * ‖l - l₀‖ := by rw [hn]
    linarith
  · calc suppFunc K l - suppFunc K l₀ ≤ C * ‖l - l₀‖ := h1
      _ < ε := hmain

/-- **Gateaux points.** Let $E$ be a real normed space, $E^*$ its continuous dual, and
$h : E^* \to \mathbb{R}$. For $x, v \in E^*$ let $h'(x; v)$ be the infimum of the difference
quotients $(h(x + t v) - h(x))/t$ over $t > 0$, taken to be $0$ when they are unbounded below.
A point $x \in E^*$ is a Gateaux point of $h$ when $h'(x; v) + h'(x; -v) \le 0$ for every
$v \in E^*$. -/
def GateauxPt (h : StrongDual ℝ E → ℝ) (x : StrongDual ℝ E) : Prop :=
  ∀ v, dirDeriv h x v + dirDeriv h x (-v) ≤ 0

omit [FiniteDimensional ℝ E] in
/-- **Strict sublevel sets of the symmetrized directional derivative are open.** Let $E$ be a
real normed space with continuous dual $E^*$, let $K \subseteq E$ be a nonempty compact set with
support function $h_K$, and write $h_K'(x; v)$ for the directional derivative of $h_K$ at $x$ in
direction $v$. For every $v \in E^*$ and every real $c$, the set of $x \in E^*$ with
$h_K'(x; v) + h_K'(x; -v) < c$ is open. -/
theorem dirDeriv_sublevel_open (hK : IsCompact K) (hKne : K.Nonempty)
    (v : StrongDual ℝ E) (c : ℝ) :
    IsOpen {x | dirDeriv (suppFunc K) x v + dirDeriv (suppFunc K) x (-v) < c} := by
  have hcont := suppFunc_continuous hK hKne
  have hinner : ∀ (t : ℝ) (w : StrongDual ℝ E),
      Continuous (fun x : StrongDual ℝ E => x + t • w) :=
    fun t w => continuous_id.add continuous_const
  have hQ : ∀ t₁ t₂ : ℝ, Continuous
      (fun x => (suppFunc K (x + t₁ • v) - suppFunc K x) / t₁
        + ((suppFunc K (x + t₂ • (-v)) - suppFunc K x) / t₂)) := by
    intro t₁ t₂
    apply Continuous.add
    · apply Continuous.div_const
      apply Continuous.sub
      · exact hcont.comp (hinner t₁ v)
      · exact hcont
    · apply Continuous.div_const
      apply Continuous.sub
      · exact hcont.comp (hinner t₂ (-v))
      · exact hcont
  have hunion : {x | dirDeriv (suppFunc K) x v + dirDeriv (suppFunc K) x (-v) < c}
      = ⋃ t₁ ∈ Ioi (0 : ℝ), ⋃ t₂ ∈ Ioi (0 : ℝ),
        {x | (suppFunc K (x + t₁ • v) - suppFunc K x) / t₁
          + ((suppFunc K (x + t₂ • (-v)) - suppFunc K x) / t₂) < c} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ioi]
    constructor
    · intro hx
      have hx' : dirDeriv (suppFunc K) x v + dirDeriv (suppFunc K) x (-v) < c := hx
      have hδ : (0 : ℝ) < (c - (dirDeriv (suppFunc K) x v
          + dirDeriv (suppFunc K) x (-v))) / 2 := by linarith
      have e1 : dirDeriv (suppFunc K) x v
          < dirDeriv (suppFunc K) x v
            + (c - (dirDeriv (suppFunc K) x v
              + dirDeriv (suppFunc K) x (-v))) / 2 := by linarith
      have e2 : dirDeriv (suppFunc K) x (-v)
          < dirDeriv (suppFunc K) x (-v)
            + (c - (dirDeriv (suppFunc K) x v
              + dirDeriv (suppFunc K) x (-v))) / 2 := by linarith
      obtain ⟨q₁, ⟨t₁, ht₁, rfl⟩, hQ₁⟩ := (csInf_lt_iff
        (dirQuot_bddBelow (suppFunc_convex hK hKne) v)
        (dirQuot_nonempty (h := suppFunc K) (x := x) v)).mp e1
      obtain ⟨q₂, ⟨t₂, ht₂, rfl⟩, hQ₂⟩ := (csInf_lt_iff
        (dirQuot_bddBelow (suppFunc_convex hK hKne) (-v))
        (dirQuot_nonempty (h := suppFunc K) (x := x) (-v))).mp e2
      simp only [] at hQ₁ hQ₂
      refine ⟨t₁, ht₁, t₂, ht₂, ?_⟩
      change (suppFunc K (x + t₁ • v) - suppFunc K x) / t₁
        + ((suppFunc K (x + t₂ • (-v)) - suppFunc K x) / t₂) < c
      linarith
    · rintro ⟨t₁, ht₁, t₂, ht₂, hx⟩
      have hx' : (suppFunc K (x + t₁ • v) - suppFunc K x) / t₁
          + ((suppFunc K (x + t₂ • (-v)) - suppFunc K x) / t₂) < c := hx
      have g1 : dirDeriv (suppFunc K) x v
          ≤ (suppFunc K (x + t₁ • v) - suppFunc K x) / t₁ :=
        dirDeriv_le_quot (suppFunc_convex hK hKne) _ ht₁
      have g2 : dirDeriv (suppFunc K) x (-v)
          ≤ (suppFunc K (x + t₂ • (-v)) - suppFunc K x) / t₂ :=
        dirDeriv_le_quot (suppFunc_convex hK hKne) _ ht₂
      change dirDeriv (suppFunc K) x v + dirDeriv (suppFunc K) x (-v) < c
      linarith
  rw [hunion]
  exact isOpen_biUnion fun t₁ ht₁ => isOpen_biUnion fun t₂ ht₂ =>
    isOpen_Iio.preimage (hQ t₁ t₂)

omit [FiniteDimensional ℝ E] in
/-- **Continuity of the directional derivative of a support function in the direction.** Let
$E$ be a real normed space with continuous dual $E^*$, let $K \subseteq E$ be a nonempty compact
set with support function $h_K$, and write $h_K'(x; w)$ for the directional derivative of $h_K$
at $x$ in direction $w$. For every $x \in E^*$, the map $w \mapsto h_K'(x; w)$ is continuous on
$E^*$. -/
theorem dirDeriv_continuous_in_v (hK : IsCompact K) (hKne : K.Nonempty)
    (x : StrongDual ℝ E) :
    Continuous (fun w => dirDeriv (suppFunc K) x w) := by
  obtain ⟨C, hC, hlip⟩ := suppFunc_lipschitz hK hKne
  have hconv := suppFunc_convex hK hKne
  have hbound : ∀ w, dirDeriv (suppFunc K) x w ≤ C * ‖w‖ := by
    intro w
    have q1 : dirDeriv (suppFunc K) x w ≤ suppFunc K (x + w) - suppFunc K x := by
      have q := dirDeriv_le_quot hconv (x := x) (v := w) (t := (1 : ℝ)) one_pos
      have e1w : x + (1 : ℝ) • w = x + w := by rw [one_smul]
      rw [e1w, div_one] at q
      exact q
    calc dirDeriv (suppFunc K) x w ≤ suppFunc K (x + w) - suppFunc K x := q1
      _ ≤ C * ‖w‖ := by
          have h := hlip (x + w) x
          rwa [add_sub_cancel_left] at h
  have hlipD : ∀ w₁ w₂, dirDeriv (suppFunc K) x w₁ - dirDeriv (suppFunc K) x w₂
      ≤ C * ‖w₁ - w₂‖ := by
    intro w₁ w₂
    have hsub := dirDeriv_subadd (x := x) hconv w₂ (w₁ - w₂)
    rw [add_sub_cancel] at hsub
    have hb := hbound (w₁ - w₂)
    linarith
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  have hCδ : ∀ ε : ℝ, 0 < ε → C * (ε / (C + 1)) ≤ ε := by
    intro ε hε
    rw [← mul_div_assoc, div_le_iff₀ hC1, mul_add, mul_one]
    linarith [mul_nonneg hC hε.le]
  rw [Metric.continuous_iff]
  intro w₀ ε hε
  refine ⟨ε / (C + 1), div_pos hε hC1, fun w hw => ?_⟩
  rw [dist_eq_norm] at hw
  have h1 := hlipD w w₀
  have h2 := hlipD w₀ w
  have hn : ‖w₀ - w‖ = ‖w - w₀‖ := by rw [← norm_neg, neg_sub]
  have hmain : C * ‖w - w₀‖ < ε := by
    by_cases hC0 : C = 0
    · rw [hC0, zero_mul]
      exact hε
    · have hCpos : 0 < C := lt_of_le_of_ne' hC hC0
      calc C * ‖w - w₀‖ < C * (ε / (C + 1)) :=
              mul_lt_mul_of_pos_left hw hCpos
        _ ≤ ε := hCδ ε hε
  rw [dist_eq_norm, Real.norm_eq_abs, abs_lt]
  constructor
  · have h2' : dirDeriv (suppFunc K) x w₀ - dirDeriv (suppFunc K) x w
        ≤ C * ‖w - w₀‖ := by
      calc dirDeriv (suppFunc K) x w₀ - dirDeriv (suppFunc K) x w
          ≤ C * ‖w₀ - w‖ := h2
        _ = C * ‖w - w₀‖ := by rw [hn]
    linarith
  · calc dirDeriv (suppFunc K) x w - dirDeriv (suppFunc K) x w₀
        ≤ C * ‖w - w₀‖ := h1
      _ < ε := hmain

omit [FiniteDimensional ℝ E] in
/-- **Lipschitz bound on directional derivatives of a support function.** Let $E$ be a real
normed space with continuous dual $E^*$, let $K \subseteq E$ be a nonempty compact set with
support function $h_K$, and write $h_K'(x; w)$ for the directional derivative of $h_K$ at $x$ in
direction $w$. If $C$ is a real number with $h_K(\ell_1) - h_K(\ell_2) \le C \|\ell_1 - \ell_2\|$
for all $\ell_1, \ell_2 \in E^*$, then $h_K'(x; w) \le C \|w\|$ for all $x, w \in E^*$. -/
theorem dirDeriv_suppFunc_bound (hK : IsCompact K) (hKne : K.Nonempty)
    {C : ℝ} (hlip : ∀ l₁ l₂ : StrongDual ℝ E,
      suppFunc K l₁ - suppFunc K l₂ ≤ C * ‖l₁ - l₂‖)
    (x w : StrongDual ℝ E) : dirDeriv (suppFunc K) x w ≤ C * ‖w‖ := by
  have hconv := suppFunc_convex hK hKne
  have q1 : dirDeriv (suppFunc K) x w ≤ suppFunc K (x + w) - suppFunc K x := by
    have q := dirDeriv_le_quot hconv (x := x) (v := w) (t := (1 : ℝ)) one_pos
    have e1w : x + (1 : ℝ) • w = x + w := by rw [one_smul]
    rw [e1w, div_one] at q
    exact q
  have h := hlip (x + w) x
  rw [add_sub_cancel_left] at h
  exact le_trans q1 h

/-- **Mazur's theorem for support functions.** Let $E$ be a finite-dimensional real normed space
with continuous dual $E^*$, let $K \subseteq E$ be a nonempty compact set with support function
$h_K$, and write $h_K'(\ell; v)$ for the directional derivative of $h_K$ at $\ell$ in direction
$v$. Then the Gateaux points of $h_K$, that is, the functionals $\ell \in E^*$ with
$h_K'(\ell; v) + h_K'(\ell; -v) \le 0$ for every $v \in E^*$, form a dense subset of $E^*$. -/
theorem dense_gateaux (hK : IsCompact K) (hKne : K.Nonempty) :
    Dense {l | GateauxPt (suppFunc K) l} := by
  rw [dense_iff_inter_open]
  intro U hUopen hUne
  by_contra hcon
  have hno : ∀ x ∈ U, ¬ GateauxPt (suppFunc K) x := by
    intro x hxU hg
    exact hcon ⟨x, hxU, hg⟩
  obtain ⟨dseq, hdseq⟩ : ∃ u : ℕ → StrongDual ℝ E, DenseRange u :=
    exists_dense_seq (α := StrongDual ℝ E)
  have hdseqD : Dense (Set.range dseq) := hdseq
  have hDcont : ∀ x : StrongDual ℝ E,
      Continuous (fun w => dirDeriv (suppFunc K) x w
        + dirDeriv (suppFunc K) x (-w)) := by
    intro x
    exact (dirDeriv_continuous_in_v hK hKne x).add
      ((dirDeriv_continuous_in_v hK hKne x).comp continuous_neg)
  set G : ℕ × ℕ → Set (StrongDual ℝ E) := fun j =>
    {x | 1 / ((j.2 : ℝ) + 1)
      ≤ dirDeriv (suppFunc K) x (dseq j.1)
        + dirDeriv (suppFunc K) x (-(dseq j.1))} with hG
  have hGclosed : ∀ j, IsClosed (G j) := by
    intro j
    have h := dirDeriv_sublevel_open hK hKne (dseq j.1) (1 / ((j.2 : ℝ) + 1))
    have heq : G j = {x | dirDeriv (suppFunc K) x (dseq j.1)
        + dirDeriv (suppFunc K) x (-(dseq j.1)) < 1 / ((j.2 : ℝ) + 1)}ᶜ := by
      ext x
      simp only [hG, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
    rw [heq]
    exact h.isClosed_compl
  have hcover : ∀ x ∈ U, ∃ j, x ∈ G j := by
    intro x hxU
    have hnx : ¬ ∀ v, dirDeriv (suppFunc K) x v + dirDeriv (suppFunc K) x (-v)
        ≤ 0 := hno x hxU
    push Not at hnx
    obtain ⟨v, hv⟩ := hnx
    have hopen : IsOpen ((fun w => dirDeriv (suppFunc K) x w
        + dirDeriv (suppFunc K) x (-w)) ⁻¹' Ioi
        ((dirDeriv (suppFunc K) x v + dirDeriv (suppFunc K) x (-v)) / 2)) :=
      isOpen_Ioi.preimage (hDcont x)
    have hne : (((fun w => dirDeriv (suppFunc K) x w
        + dirDeriv (suppFunc K) x (-w)) ⁻¹' Ioi
        ((dirDeriv (suppFunc K) x v + dirDeriv (suppFunc K) x (-v)) / 2)) :
        Set _).Nonempty := by
      refine ⟨v, ?_⟩
      change (dirDeriv (suppFunc K) x v + dirDeriv (suppFunc K) x (-v)) / 2
        < dirDeriv (suppFunc K) x v + dirDeriv (suppFunc K) x (-v)
      linarith
    obtain ⟨_, ⟨n, rfl⟩, hmem⟩ := hdseqD.exists_mem_open hopen hne
    have hmem' : (dirDeriv (suppFunc K) x v + dirDeriv (suppFunc K) x (-v)) / 2
        < dirDeriv (suppFunc K) x (dseq n)
          + dirDeriv (suppFunc K) x (-(dseq n)) := hmem
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (by linarith :
      (0 : ℝ) < dirDeriv (suppFunc K) x (dseq n)
        + dirDeriv (suppFunc K) x (-(dseq n)))
    refine ⟨(n, k), ?_⟩
    change 1 / ((k : ℝ) + 1) ≤ _
    exact hk.le
  obtain ⟨e', he'U⟩ := hUne
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds he'U)
  set ρ := ε / 2 with hρ
  have hρpos : 0 < ρ := by linarith
  have hBU : closedBall e' ρ ⊆ U := by
    intro z hz
    apply hεU
    have hzd : dist z e' ≤ ρ := Metric.mem_closedBall.mp hz
    rw [Metric.mem_ball]
    linarith
  set C : ℕ × ℕ → Set ↥(closedBall e' ρ) := fun j =>
    Subtype.val ⁻¹' (G j) with hC
  have hCclosed : ∀ j, IsClosed (C j) := by
    intro j
    exact isClosed_induced_iff.mpr ⟨G j, hGclosed j, rfl⟩
  have hcovB : ∀ y : ↥(closedBall e' ρ), ∃ j, y ∈ C j := by
    intro y
    have hyU : (y : StrongDual ℝ E) ∈ U := hBU y.2
    obtain ⟨j, hj⟩ := hcover _ hyU
    exact ⟨j, hj⟩
  have hex : ∃ j, (interior (C j)).Nonempty := by
    by_contra hnone
    push Not at hnone
    have hUopen' : ∀ j, IsOpen ((C j)ᶜ) := fun j => (hCclosed j).isOpen_compl
    have hUdense : ∀ j, Dense ((C j)ᶜ) := by
      intro j
      rw [dense_iff_closure_eq, closure_compl, hnone j, Set.compl_empty]
    have hdense := dense_iInter_of_isOpen (f := fun j => (C j)ᶜ) hUopen' hUdense
    have huniv : (⋃ j, C j) = univ := by
      apply subset_antisymm (subset_univ _)
      intro y _
      obtain ⟨j, hj⟩ := hcovB y
      exact Set.mem_iUnion.mpr ⟨j, hj⟩
    have hempty : (⋂ j, (C j)ᶜ) = ∅ := by
      rw [← Set.compl_iUnion, huniv, Set.compl_univ]
    rw [hempty] at hdense
    have hy₀ : (⟨e', Metric.mem_closedBall.mpr (by rw [dist_self]; exact hρpos.le)⟩ :
        ↥(closedBall e' ρ)) ∈ closure (∅ : Set ↥(closedBall e' ρ)) := hdense _
    rw [closure_empty] at hy₀
    exact (Set.notMem_empty _ hy₀).elim
  obtain ⟨⟨n, k⟩, hjint⟩ := hex
  obtain ⟨z, hzint⟩ := hjint
  have hzC : z ∈ C (n, k) := interior_subset hzint
  obtain ⟨W₀, hW₀open, hW₀eq⟩ :=
    isOpen_induced_iff (f := Subtype.val).mp (isOpen_interior (s := C (n, k)))
  have hzW₀ : (z : StrongDual ℝ E) ∈ W₀ := by
    rw [← Set.mem_preimage, hW₀eq]
    exact hzint
  have hW₀B : ∀ w ∈ W₀, w ∈ closedBall e' ρ → w ∈ G (n, k) := by
    intro w hwW hwB
    have h1 : (⟨w, hwB⟩ : ↥(closedBall e' ρ)) ∈ interior (C (n, k)) := by
      rw [← hW₀eq]
      exact hwW
    have h2 : (⟨w, hwB⟩ : ↥(closedBall e' ρ)) ∈ C (n, k) :=
      interior_subset h1
    exact h2
  -- point of W₀ strictly inside the ball, via the segment from e'
  have hseg : ∃ z' ∈ W₀ ∩ ball e' ρ, True := by
    have hcont_g : Continuous (fun s : ℝ => (1 - s) • e' + s • (z : StrongDual ℝ E)) :=
      (continuous_const.sub continuous_id).smul continuous_const |>.add
        (continuous_id.smul continuous_const)
    have hg1 : (fun s : ℝ => (1 - s) • e' + s • (z : StrongDual ℝ E)) 1
        = (z : StrongDual ℝ E) := by
      simp [sub_self, zero_smul, zero_add, one_smul]
    have hmem : (1 : ℝ) ∈ (fun s : ℝ => (1 - s) • e' + s • (z : StrongDual ℝ E)) ⁻¹' W₀ := by
      change _ ∈ W₀
      rw [hg1]
      exact hzW₀
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp
      ((hW₀open.preimage hcont_g).mem_nhds hmem)
    -- s := 1 - min (δ/2) (1/2)
    set m := min (δ / 2) (1 / 2 : ℝ) with hm
    have hmpos : 0 < m := lt_min (by linarith) (by norm_num)
    have hmle : m ≤ 1 / 2 := min_le_right _ _
    have hmd : m < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    set s := 1 - m with hs
    have hs01 : 0 < s ∧ s < 1 := ⟨by linarith, by linarith⟩
    have hsin : s ∈ ball (1 : ℝ) δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have : ‖s - 1‖ = m := by
        rw [hs]
        have : (1 - m) - 1 = -m := by ring
        rw [this, norm_neg]
        have : ‖m‖ = m := by rw [Real.norm_eq_abs, abs_of_pos hmpos]
        exact this
      rw [this]
      exact hmd
    have hgsW : (1 - s) • e' + s • (z : StrongDual ℝ E) ∈ W₀ := hδsub hsin
    have hdist : dist ((1 - s) • e' + s • (z : StrongDual ℝ E)) e'
        = s * dist (z : StrongDual ℝ E) e' := by
      have e_seg : (1 - s) • e' + s • (z : StrongDual ℝ E) - e'
          = s • ((z : StrongDual ℝ E) - e') := by
        module
      rw [dist_eq_norm, e_seg, norm_smul, Real.norm_eq_abs, abs_of_pos hs01.1, dist_eq_norm]
    have hzB : dist (z : StrongDual ℝ E) e' ≤ ρ := Metric.mem_closedBall.mp z.2
    have hlt : dist ((1 - s) • e' + s • (z : StrongDual ℝ E)) e' < ρ := by
      rw [hdist]
      have h3 : s * dist (z : StrongDual ℝ E) e' ≤ s * ρ :=
        mul_le_mul_of_nonneg_left hzB hs01.1.le
      have h4 : s * ρ < ρ := by
        have h5 : s * ρ < 1 * ρ := mul_lt_mul_of_pos_right hs01.2 hρpos
        rwa [one_mul] at h5
      linarith
    exact ⟨(1 - s) • e' + s • (z : StrongDual ℝ E),
      ⟨hgsW, Metric.mem_ball.mpr hlt⟩, trivial⟩
  obtain ⟨z', hz'W, -⟩ := hseg
  -- V := W₀ ∩ ball e' ρ
  set V : Set (StrongDual ℝ E) := W₀ ∩ ball e' ρ with hV
  have hVopen : IsOpen V := hW₀open.inter isOpen_ball
  have hVne : V.Nonempty := ⟨z', hz'W⟩
  have hVG : ∀ w ∈ V, w ∈ G (n, k) := by
    intro w hw
    exact hW₀B w hw.1 (Metric.ball_subset_closedBall hw.2)
  -- 1D contradiction on the line through z' in direction dseq n
  obtain ⟨y₀, hy₀V⟩ := hVne
  by_cases hv0 : dseq n = 0
  · have hmem : dirDeriv (suppFunc K) y₀ (dseq n)
        + dirDeriv (suppFunc K) y₀ (-(dseq n)) ≥ 1 / ((k : ℝ) + 1) := hVG y₀ hy₀V
    rw [hv0] at hmem
    simp only [neg_zero, dirDeriv_zero] at hmem
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := one_div_pos.mpr (by positivity)
    linarith
  · -- slope growth contradiction
    have hcont_l : Continuous (fun t : ℝ => y₀ + t • dseq n) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hpre : (0 : ℝ) ∈ (fun t : ℝ => y₀ + t • dseq n) ⁻¹' V := by
      change y₀ + (0 : ℝ) • dseq n ∈ V
      rw [zero_smul, add_zero]
      exact hy₀V
    obtain ⟨η, hηpos, hηsub⟩ := Metric.mem_nhds_iff.mp
      ((hVopen.preimage hcont_l).mem_nhds hpre)
    have hmemV : ∀ t : ℝ, |t| < η → y₀ + t • dseq n ∈ V := by
      intro t ht
      have htball : t ∈ ball (0 : ℝ) η := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hnorm : ‖t - 0‖ = |t| := by rw [sub_zero, Real.norm_eq_abs]
        rw [hnorm]
        exact ht
      exact hηsub htball
    set a := -η / 2 with ha
    set b := η / 2 with hb
    have hab : a < b := by linarith
    have haV : y₀ + a • dseq n ∈ V :=
      hmemV a (by rw [ha, abs_div, abs_neg, abs_of_pos hηpos,
        abs_of_pos (show (0:ℝ) < 2 from by norm_num)]; linarith)
    have hbV : y₀ + b • dseq n ∈ V :=
      hmemV b (by rw [hb, abs_div, abs_of_pos hηpos,
        abs_of_pos (show (0:ℝ) < 2 from by norm_num)]; linarith)
    have growth : ∀ s t' : ℝ, y₀ + s • dseq n ∈ V → y₀ + t' • dseq n ∈ V →
        s < t' → dirDeriv (suppFunc K) (y₀ + t' • dseq n) (dseq n)
          - dirDeriv (suppFunc K) (y₀ + s • dseq n) (dseq n) ≥ 1 / ((k : ℝ) + 1) := by
      intro s t' hs ht' hst
      have e : (y₀ + s • dseq n) + (t' - s) • dseq n = y₀ + t' • dseq n := by
        module
      have q1 := dirDeriv_le_quot (suppFunc_convex hK hKne) (x := y₀ + s • dseq n)
        (dseq n) (show (0 : ℝ) < t' - s by linarith)
      rw [e] at q1
      have e' : (y₀ + t' • dseq n) + (t' - s) • (-(dseq n)) = y₀ + s • dseq n := by
        module
      have q2 := dirDeriv_le_quot (suppFunc_convex hK hKne) (x := y₀ + t' • dseq n)
        (-(dseq n)) (show (0 : ℝ) < t' - s by linarith)
      rw [e'] at q2
      have hmem := hVG _ ht'
      have hmem' : dirDeriv (suppFunc K) (y₀ + t' • dseq n) (dseq n)
          + dirDeriv (suppFunc K) (y₀ + t' • dseq n) (-(dseq n))
          ≥ 1 / ((k : ℝ) + 1) := hmem
      have qneg : (suppFunc K (y₀ + s • dseq n) - suppFunc K (y₀ + t' • dseq n))
          / (t' - s)
          = -((suppFunc K (y₀ + t' • dseq n) - suppFunc K (y₀ + s • dseq n))
            / (t' - s)) := by ring
      rw [qneg] at q2
      linarith
    -- equally spaced points, telescoping
    have key : ∀ N : ℕ, ((N : ℝ) + 1) / ((k : ℝ) + 1)
        ≤ dirDeriv (suppFunc K) (y₀ + b • dseq n) (dseq n)
          - dirDeriv (suppFunc K) (y₀ + a • dseq n) (dseq n) := by
      intro N
      have hstep : ∀ i ∈ Finset.range (N + 1),
          dirDeriv (suppFunc K) (y₀ + (a + ((i : ℝ) + 1) * ((b - a) / (N + 1))) • dseq n) (dseq n)
            - dirDeriv (suppFunc K) (y₀ + (a + (i : ℝ) * ((b - a) / (N + 1))) • dseq n) (dseq n)
            ≥ 1 / ((k : ℝ) + 1) := by
        intro i hi
        apply growth
        · apply hmemV
          have : |a + (i : ℝ) * ((b - a) / (N + 1))| ≤ η / 2 := by
            have hiN : (i : ℝ) ≤ N := by
              have := Finset.mem_range.mp hi
              exact Nat.cast_le.mpr (Nat.lt_succ_iff.mp this)
            rw [ha, hb]
            have hba : (0 : ℝ) ≤ (η / 2 - -η / 2) / (N + 1) := by positivity
            have hub : -η / 2 + (i : ℝ) * ((η / 2 - -η / 2) / (N + 1)) ≤ η / 2 := by
              have : (i : ℝ) * ((η / 2 - -η / 2) / (N + 1)) ≤ N * ((η / 2 - -η / 2) / (N + 1)) :=
                mul_le_mul_of_nonneg_right hiN hba
              have eNN : (N : ℝ) * ((η / 2 - -η / 2) / (N + 1)) =
                η / 2 - -η / 2 - (η / 2 - -η / 2) / (N + 1) := by
                field_simp
                ring
              linarith
            have hlb : -η / 2 ≤ -η / 2 + (i : ℝ) * ((η / 2 - -η / 2) / (N + 1)) := by
              have : (0 : ℝ) ≤ (i : ℝ) * ((η / 2 - -η / 2) / (N + 1)) :=
                mul_nonneg (Nat.cast_nonneg _) hba
              linarith
            rw [abs_le]
            constructor <;> linarith
          linarith
        · apply hmemV
          have : |a + ((i : ℝ) + 1) * ((b - a) / (N + 1))| ≤ η / 2 := by
            have hiN : (i : ℝ) ≤ N := by
              have := Finset.mem_range.mp hi
              exact Nat.cast_le.mpr (Nat.lt_succ_iff.mp this)
            have hiN1 : ((i : ℝ) + 1) ≤ N + 1 := by linarith
            rw [ha, hb]
            have hba : (0 : ℝ) ≤ (η / 2 - -η / 2) / (N + 1) := by positivity
            have hub : -η / 2 + ((i : ℝ) + 1) * ((η / 2 - -η / 2) / (N + 1)) ≤ η / 2 := by
              have : ((i : ℝ) + 1) * ((η / 2 - -η / 2) / (N + 1))
                  ≤ (N + 1) * ((η / 2 - -η / 2) / (N + 1)) :=
                mul_le_mul_of_nonneg_right hiN1 hba
              have eNN : ((N : ℝ) + 1) * ((η / 2 - -η / 2) / (N + 1))
                  = η / 2 - -η / 2 := by
                field_simp
              linarith
            have hlb : -η / 2 ≤ -η / 2 + ((i : ℝ) + 1) * ((η / 2 - -η / 2) / (N + 1)) := by
              have : (0 : ℝ) ≤ ((i : ℝ) + 1) * ((η / 2 - -η / 2) / (N + 1)) :=
                mul_nonneg (by positivity) hba
              linarith
            rw [abs_le]
            constructor <;> linarith
          linarith
        · -- s < t'
          have hpos : (0 : ℝ) < (b - a) / (N + 1) := by
            apply div_pos _ (by positivity)
            linarith
          have : a + (i : ℝ) * ((b - a) / (N + 1))
              < a + ((i : ℝ) + 1) * ((b - a) / (N + 1)) := by
            have : (i : ℝ) * ((b - a) / (N + 1))
                < ((i : ℝ) + 1) * ((b - a) / (N + 1)) := by
              apply mul_lt_mul_of_pos_right _ hpos
              linarith
            linarith
          exact this
      have hsum := Finset.sum_le_sum hstep
      -- telescope
      have htel : ∑ i ∈ Finset.range (N + 1),
          (dirDeriv (suppFunc K) (y₀ + (a + ((i : ℝ) + 1) * ((b - a) / (N + 1))) • dseq n) (dseq n)
            - dirDeriv (suppFunc K) (y₀ + (a + (i : ℝ) * ((b - a) / (N + 1))) • dseq n) (dseq n))
          = dirDeriv (suppFunc K) (y₀ + b • dseq n) (dseq n)
            - dirDeriv (suppFunc K) (y₀ + a • dseq n) (dseq n) := by
        have eN : a + ((N : ℝ) + 1) * ((b - a) / (N + 1)) = b := by
          field_simp
          ring
        have e0 : a + ((0 : ℝ)) * ((b - a) / (N + 1)) = a := by ring
        have hNcast : ((N + 1 : ℕ) : ℝ) = ((N : ℝ) + 1) := by push_cast; ring
        have hfN : dirDeriv (suppFunc K)
              (y₀ + (a + (((N + 1 : ℕ)) : ℝ) * ((b - a) / (N + 1))) • dseq n) (dseq n)
            = dirDeriv (suppFunc K) (y₀ + b • dseq n) (dseq n) := by
          rw [hNcast, eN]
        have hf0 : dirDeriv (suppFunc K)
              (y₀ + (a + (((0 : ℕ)) : ℝ) * ((b - a) / (N + 1))) • dseq n) (dseq n)
            = dirDeriv (suppFunc K) (y₀ + a • dseq n) (dseq n) := by
          rw [Nat.cast_zero, e0]
        have hterm : ∀ i ∈ Finset.range (N + 1),
            (dirDeriv (suppFunc K)
              (y₀ + (a + ((i : ℝ) + 1) * ((b - a) / (N + 1))) • dseq n) (dseq n)
              - dirDeriv (suppFunc K) (y₀ + (a + (i : ℝ) * ((b - a) / (N + 1))) • dseq n) (dseq n))
            = ((fun j : ℕ =>
              dirDeriv (suppFunc K) (y₀ + (a + (j : ℝ) * ((b - a) / (N + 1))) • dseq n)
                (dseq n)) (i + 1)
            - (fun j : ℕ =>
              dirDeriv (suppFunc K) (y₀ + (a + (j : ℝ) * ((b - a) / (N + 1))) • dseq n)
                (dseq n)) i) := by
          intro i hi
          have hss : a + ((i : ℝ) + 1) * ((b - a) / (N + 1))
              = a + (((i + 1 : ℕ)) : ℝ) * ((b - a) / (N + 1)) := by
            push_cast
            ring
          rw [hss]
        have hsum_eq : (∑ i ∈ Finset.range (N + 1),
              (dirDeriv (suppFunc K)
                (y₀ + (a + ((i : ℝ) + 1) * ((b - a) / (N + 1))) • dseq n) (dseq n)
                - dirDeriv (suppFunc K)
                  (y₀ + (a + (i : ℝ) * ((b - a) / (N + 1))) • dseq n) (dseq n)))
            = ∑ i ∈ Finset.range (N + 1),
              ((fun j : ℕ =>
                dirDeriv (suppFunc K) (y₀ + (a + (j : ℝ) * ((b - a) / (N + 1))) • dseq n)
                  (dseq n)) (i + 1)
              - (fun j : ℕ =>
                dirDeriv (suppFunc K) (y₀ + (a + (j : ℝ) * ((b - a) / (N + 1))) • dseq n)
                  (dseq n)) i) :=
          Finset.sum_congr rfl (fun i hi => hterm i hi)
        have e := Finset.sum_range_sub (fun j : ℕ =>
          dirDeriv (suppFunc K)
            (y₀ + (a + (j : ℝ) * ((b - a) / (N + 1))) • dseq n) (dseq n)) (N + 1)
        rw [hsum_eq, e, hfN, hf0]
      have hcard : ∑ i ∈ Finset.range (N + 1), (1 / ((k : ℝ) + 1))
          = ((N : ℝ) + 1) / ((k : ℝ) + 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
      calc ((N : ℝ) + 1) / ((k : ℝ) + 1)
          = ∑ i ∈ Finset.range (N + 1), (1 / ((k : ℝ) + 1)) := hcard.symm
        _ ≤ ∑ i ∈ Finset.range (N + 1),
            (dirDeriv (suppFunc K)
              (y₀ + (a + ((i : ℝ) + 1) * ((b - a) / (N + 1))) • dseq n) (dseq n)
              - dirDeriv (suppFunc K)
                (y₀ + (a + (i : ℝ) * ((b - a) / (N + 1))) • dseq n) (dseq n)) := hsum
        _ = dirDeriv (suppFunc K) (y₀ + b • dseq n) (dseq n)
            - dirDeriv (suppFunc K) (y₀ + a • dseq n) (dseq n) := htel
    -- unbounded linear growth contradicts the Lipschitz bound on directional derivatives
    obtain ⟨C, hC, hlip⟩ := suppFunc_lipschitz hK hKne
    have hBb : dirDeriv (suppFunc K) (y₀ + b • dseq n) (dseq n) ≤ C * ‖dseq n‖ :=
      dirDeriv_suppFunc_bound hK hKne hlip _ _
    have hBa_neg : dirDeriv (suppFunc K) (y₀ + a • dseq n) (-(dseq n))
        ≤ C * ‖dseq n‖ := by
      have h := dirDeriv_suppFunc_bound hK hKne hlip (y₀ + a • dseq n) (-(dseq n))
      rwa [norm_neg] at h
    have hnonneg : (0 : ℝ) ≤ dirDeriv (suppFunc K) (y₀ + a • dseq n) (dseq n)
        + dirDeriv (suppFunc K) (y₀ + a • dseq n) (-(dseq n)) :=
      dirDeriv_add_neg_nonneg (suppFunc_convex hK hKne) (dseq n)
    have hle : dirDeriv (suppFunc K) (y₀ + b • dseq n) (dseq n)
        - dirDeriv (suppFunc K) (y₀ + a • dseq n) (dseq n)
        ≤ 2 * C * ‖dseq n‖ := by linarith
    have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * C * ‖dseq n‖ * ((k : ℝ) + 1))
    have hkey := key N
    have hfin : ((N : ℝ) + 1) ≤ 2 * C * ‖dseq n‖ * ((k : ℝ) + 1) := by
      have hle' := le_trans hkey hle
      have h := (div_le_iff₀ hkpos).mp hle'
      linarith
    have hN' : 2 * C * ‖dseq n‖ * ((k : ℝ) + 1) < (N : ℝ) := hN
    linarith
end Support

section GateauxExposed

set_option linter.unusedVariables false in
omit [FiniteDimensional ℝ E] in
/-- **A maximizer bounds the directional derivative of the support function from below.** Let
$K$ be a nonempty compact subset of a real normed space $E$, let $h_K(l) = \sup_{y \in K} l(y)$
be its support function on the continuous dual $E^*$, and write $h_K'(u; v)$ for the
directional derivative of $h_K$ at $u$ in direction $v$. If $u \in E^*$ and $z \in K$ satisfy
$u(z) = h_K(u)$, then $v(z) \le h_K'(u; v)$ for every $v \in E^*$. -/
theorem maximizer_dirDeriv_ge {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    {u : StrongDual ℝ E} {z : E} (hzK : z ∈ K) (hmax : u z = suppFunc K u)
    (v : StrongDual ℝ E) : v z ≤ dirDeriv (suppFunc K) u v := by
  unfold dirDeriv
  apply le_csInf (dirQuot_nonempty v)
  rintro b ⟨t, ht, rfl⟩
  have hcont : Continuous (fun x => (u + t • v) x) :=
    ((u + t • v) : E →L[ℝ] ℝ).continuous
  have hbdd : BddAbove ((fun x => (u + t • v) x) '' K) := (hK.image hcont).bddAbove
  have hsup : (u + t • v) z ≤ suppFunc K (u + t • v) :=
    le_csSup hbdd ⟨z, hzK, rfl⟩
  have e : (u + t • v) z = u z + t * v z := by
    simp [add_apply, smul_apply, smul_eq_mul]
  have ht' : (0 : ℝ) < t := ht
  rw [e, hmax] at hsup
  have key : v z * t ≤ suppFunc K (u + t • v) - suppFunc K u := by
    rw [mul_comm]
    linarith
  exact (le_div_iff₀ ht').mpr key

omit [FiniteDimensional ℝ E] in
/-- **Maximizers at a Gateaux point of the support function are unique.** Let $K$ be a
nonempty compact subset of a real normed space $E$, and let $h_K(l) = \sup_{y \in K} l(y)$ be its
support function on the continuous dual $E^*$. If $l \in E^*$ is a Gateaux point of $h_K$ and
$z_1, z_2 \in K$ satisfy $l(z_1) = h_K(l)$ and $l(z_2) = h_K(l)$, then $z_1 = z_2$. -/
theorem gateaux_unique_maximizer {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    {l : StrongDual ℝ E} (hG : GateauxPt (suppFunc K) l)
    {z₁ z₂ : E} (h₁ : z₁ ∈ K) (h₂ : z₂ ∈ K)
    (e₁ : l z₁ = suppFunc K l) (e₂ : l z₂ = suppFunc K l) : z₁ = z₂ := by
  have hD : ∀ v : StrongDual ℝ E, dirDeriv (suppFunc K) l v = v z₁ := by
    intro v
    apply le_antisymm
    · have h1v := maximizer_dirDeriv_ge hK hKne h₁ e₁ v
      have h2v := maximizer_dirDeriv_ge hK hKne h₁ e₁ (-v)
      have hGv := hG v
      have hsm : (-v) z₁ = -(v z₁) := by simp
      rw [hsm] at h2v
      linarith
    · exact maximizer_dirDeriv_ge hK hKne h₁ e₁ v
  by_contra hne
  obtain ⟨f, hf⟩ := geometric_hahn_banach_point_point hne
  have h1f := maximizer_dirDeriv_ge hK hKne h₂ e₂ f
  rw [hD f] at h1f
  linarith

set_option linter.unusedVariables false in
omit [FiniteDimensional ℝ E] in
/-- **A unique maximizer of a linear functional is an exposed point.** Let $K$ be a nonempty
compact set in a real normed space $E$, let $\ell$ be a continuous linear functional on $E$, and
let $h_K$ be the support function of $K$. If $z \in K$ satisfies $\ell(z) = h_K(\ell)$ and every
$y \in K$ with $\ell(y) = h_K(\ell)$ equals $z$, then $z$ is an exposed point of $K$. -/
theorem unique_maximizer_exposed {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    {l : StrongDual ℝ E} {z : E} (hzK : z ∈ K) (hmax : l z = suppFunc K l)
    (huniq : ∀ y ∈ K, l y = suppFunc K l → y = z) :
    z ∈ K.exposedPoints ℝ := by
  have hcont : Continuous (fun x => l x) := (l : E →L[ℝ] ℝ).continuous
  have hbdd : BddAbove ((fun x => l x) '' K) := (hK.image hcont).bddAbove
  have hle : ∀ y ∈ K, l y ≤ l z := by
    intro y hy
    have h : l y ≤ suppFunc K l :=
      le_csSup hbdd (⟨y, hy, rfl⟩ : l y ∈ (fun x => l x) '' K)
    rwa [← hmax] at h
  rw [exposed_point_def]
  exact ⟨hzK, l, fun y hy => ⟨hle y hy, fun h => huniq y hy (le_antisymm (hle y hy) h ▸ hmax)⟩⟩

end GateauxExposed

section StraszewiczMain

/-- Straszewicz's theorem: every extreme point of a compact convex set in finite
dimensions lies in the closure of the exposed points. -/
theorem straszewicz_theorem {A : Set E} (hA_compact : IsCompact A)
    (hA_convex : Convex ℝ A) :
    A.extremePoints ℝ ⊆ closure (A.exposedPoints ℝ) := by
  intro x hx
  rw [hA_convex.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff] at hx
  obtain ⟨hxA, hxhull⟩ := hx
  have hAne : A.Nonempty := ⟨x, hxA⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hop : ∀ a b : StrongDual ℝ E, ∀ y : E, a y - b y ≤ ‖a - b‖ * ‖y‖ := by
    intro a b y
    have e : a y - b y = (a - b) y := by rw [sub_apply]
    rw [e]
    calc (a - b) y ≤ ‖(a - b) y‖ := le_abs_self _
      _ ≤ ‖a - b‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
  obtain ⟨xB, hxBK, hBmax⟩ :=
    hA_compact.exists_isMaxOn hAne continuous_norm.continuousOn
  have hBmax' : ∀ y ∈ A, ‖y‖ ≤ ‖xB‖ := fun y hy => hBmax hy
  set B : Set E := A \ Metric.ball x ε with hBdef
  have hBsub : B ⊆ A \ {x} := by
    intro y hy
    obtain ⟨hyA, hyB⟩ := hy
    refine ⟨hyA, fun hmem => ?_⟩
    rw [Set.mem_singleton_iff] at hmem
    have hmem2 : y ∈ Metric.ball x ε := by
      rw [hmem]
      exact Metric.mem_ball_self hε
    exact hyB hmem2
  have hxB : x ∉ convexHull ℝ B := fun h => hxhull (convexHull_mono hBsub h)
  have hBcompact : IsCompact B := by
    have hbeq : B = A ∩ (Metric.ball x ε)ᶜ := Set.sdiff_eq _ _
    rw [hbeq]
    exact hA_compact.inter_right Metric.isOpen_ball.isClosed_compl
  have hScompact : IsCompact (convexHull ℝ B) := IsCompact.convexHull_of_compact hBcompact
  obtain ⟨f, u, hfu, hux⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ B) hScompact.isClosed hxB
  have hδ : (0 : ℝ) < f x - u := sub_pos.mpr hux
  set S : ℝ := ‖x‖ + ‖xB‖ + 1 with hSdef
  have h2S : (0 : ℝ) < 2 * S := by
    rw [hSdef]
    have h1 := norm_nonneg x
    have h2 := norm_nonneg xB
    linarith
  set ρ : ℝ := (f x - u) / (2 * S) with hρdef
  have hρpos : 0 < ρ := div_pos hδ h2S
  have hdense := dense_gateaux hA_compact hAne
  rw [dense_iff_closure_eq] at hdense
  have hmem : f ∈ closure {l | GateauxPt (suppFunc A) l} := by
    rw [hdense]
    exact Set.mem_univ f
  obtain ⟨l', hl'G, hl'dist⟩ := Metric.mem_closure_iff.mp hmem ρ hρpos
  have hl'G' : GateauxPt (suppFunc A) l' := hl'G
  obtain ⟨z', hz'K, hz'max⟩ := suppFunc_attain hA_compact hAne l'
  have huniq : ∀ y ∈ A, l' y = suppFunc A l' → y = z' :=
    fun y hy he => gateaux_unique_maximizer hA_compact hAne hl'G' hy hz'K he hz'max
  refine ⟨z', unique_maximizer_exposed hA_compact hAne hz'K hz'max huniq, ?_⟩
  by_contra hz'ball
  have hz'B : z' ∈ B := ⟨hz'K, fun h => hz'ball (Metric.mem_ball'.mp h)⟩
  have hfz' : f z' < u := hfu _ (subset_convexHull ℝ B hz'B)
  have hnorm : ‖f - l'‖ < ρ := by
    have h1 : dist f l' < ρ := hl'dist
    rwa [dist_eq_norm] at h1
  have hnorm2 : ‖l' - f‖ < ρ := by
    have h1 : dist f l' < ρ := hl'dist
    rw [dist_comm] at h1
    rwa [dist_eq_norm] at h1
  have e1 : f x - l' x ≤ ρ * ‖x‖ := by
    calc f x - l' x ≤ ‖f - l'‖ * ‖x‖ := hop f l' x
      _ ≤ ρ * ‖x‖ := mul_le_mul_of_nonneg_right (le_of_lt hnorm) (norm_nonneg _)
  have e2 : l' z' - f z' ≤ ρ * ‖xB‖ :=
    calc l' z' - f z' ≤ ‖l' - f‖ * ‖z'‖ := hop l' f z'
      _ ≤ ρ * ‖xB‖ :=
          mul_le_mul (le_of_lt hnorm2) (hBmax' z' hz'K) (norm_nonneg _) hρpos.le
  have hmax' : l' x ≤ l' z' := by
    have hcont : Continuous (fun y => l' y) := ((l') : E →L[ℝ] ℝ).continuous
    have hbdd : BddAbove ((fun y => l' y) '' A) := (hA_compact.image hcont).bddAbove
    have h : l' x ≤ suppFunc A l' :=
      le_csSup hbdd (⟨x, hxA, rfl⟩ : l' x ∈ (fun y => l' y) '' A)
    rwa [← hz'max] at h
  have hδS : f x - u < ρ * (‖x‖ + ‖xB‖) := by
    have hdecomp : f x - u
        = (f x - l' x) + (l' x - l' z') + (l' z' - f z') + (f z' - u) := by ring
    rw [hdecomp]
    have hneg1 : l' x - l' z' ≤ 0 := sub_nonpos.mpr hmax'
    have hneg2 : f z' - u < 0 := sub_neg.mpr hfz'
    calc (f x - l' x) + (l' x - l' z') + (l' z' - f z') + (f z' - u)
        < ρ * ‖x‖ + 0 + ρ * ‖xB‖ + 0 := by
          apply add_lt_add_of_le_of_lt
          · exact add_le_add (add_le_add e1 hneg1) e2
          · exact hneg2
      _ = ρ * (‖x‖ + ‖xB‖) := by ring
  have hSx : ‖x‖ + ‖xB‖ < 2 * S := by
    rw [hSdef]
    have h1 := norm_nonneg x
    have h2 := norm_nonneg xB
    linarith
  have hfrac : (‖x‖ + ‖xB‖) / (2 * S) < 1 := (div_lt_one h2S).mpr hSx
  have hlt : ρ * (‖x‖ + ‖xB‖) < f x - u := by
    have hρe : ρ * (‖x‖ + ‖xB‖) = (f x - u) * ((‖x‖ + ‖xB‖) / (2 * S)) := by
      rw [hρdef]
      ring
    rw [hρe]
    have h := mul_lt_mul_of_pos_left hfrac hδ
    rwa [mul_one] at h
  linarith

end StraszewiczMain

end MathlibExt.Analysis.Convex.Straszewicz
