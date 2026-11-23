/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Parametrized Euclidean links, ambient isotopy, and type ropelength
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import MathlibExt.Geometry.Euclidean.Ropelength

@[expose] public section

open MathlibExt.Geometry.Euclidean.Ropelength

namespace MathlibExt.Topology.Knot.Euclidean

/-!
# Parametrized Euclidean links and ambient isotopy

A parametrized knot is a smooth injective immersion `ℝ → ℝ³` of period
`2π`, injective on one period. A parametrized link is a finite labeled
family of such knots with pairwise disjoint traces. Ambient isotopy is
represented by jointly smooth forward and inverse families of
diffeomorphisms of `ℝ³`, starting at the identity, together with
orientation-preserving reparametrizations of each component.

The parametrization and component labels are retained. Consequently
isotopy in this file is oriented, labeled ambient isotopy. Unlabeled
link isotopy, diagrammatic Reidemeister equivalence, regular
projections, crossing number, and alternation are later layers.

On top of the one-curve quantities in
`MathlibExt.Geometry.Euclidean.Ropelength`, this file defines a link's
total contour length, its whole-trace ropelength ratio, and the
ropelength of its ambient-isotopy type as the infimum over isotopic
representatives.

`ParametrizedKnot`, `AmbientIsotopy`, and `CircleReparam` deliberately
match, field for field, the `Knot`, `AmbientIsotopy`, and
`CircleReparam` of `WantedExt.Topology.ConwayKnotShared`. That file is
a trusted verbatim copy of lean-eval helpers and MathlibExt cannot
import WantedExt, so this file is the canonical working copy instead;
`WantedExt.Topology.ConwayKnotEuclideanBridge` proves the two APIs
interoperate (fieldwise equivalences and isotopy transfer) without
modifying either definition.
-/

/-- **Parametrized knot.** An oriented parametrized smooth knot in Euclidean 3-space is a
$C^\infty$ curve $\gamma \colon \mathbb{R} \to \mathbb{R}^3$ that is $2\pi$-periodic
($\gamma(t + 2\pi) = \gamma(t)$ for all $t$), injective on $[0, 2\pi)$, and an immersion
($\gamma'(t) \neq 0$ for all $t$). -/
structure ParametrizedKnot where
  curve : ℝ → R3
  smooth : ContDiff ℝ (⊤ : ℕ∞) curve
  periodic : ∀ t, curve (t + 2 * Real.pi) = curve t
  injOn : Set.InjOn curve (Set.Ico 0 (2 * Real.pi))
  immersion : ∀ t, deriv curve t ≠ 0

/-- **Parametrized link.** An oriented labeled parametrized smooth link with $n$ components
in Euclidean 3-space is a family $(\gamma_i)_{i < n}$ of parametrized knots whose traces
$\gamma_i(\mathbb{R})$ are pairwise disjoint. -/
structure ParametrizedLink (n : ℕ) where
  component : Fin n → ParametrizedKnot
  pairwiseDisjoint : Set.PairwiseDisjoint (Set.univ : Set (Fin n))
    (fun i => Set.range (component i).curve)

/-- **Smooth ambient isotopy of Euclidean 3-space.** A smooth ambient isotopy of
$\mathbb{R}^3$ consists of two families of maps $H_t, G_t \colon \mathbb{R}^3 \to \mathbb{R}^3$,
indexed by times $t \in \mathbb{R}$, such that $(t, x) \mapsto H_t(x)$ and
$(t, x) \mapsto G_t(x)$ are $C^\infty$ on $\mathbb{R} \times \mathbb{R}^3$, $G_t(H_t(x)) = x$
and $H_t(G_t(x)) = x$ for all $t$ and $x$, and $H_0$ is the identity. -/
structure AmbientIsotopy where
  H : ℝ → R3 → R3
  Hinv : ℝ → R3 → R3
  smooth : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry H)
  smooth_inv : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Hinv)
  inv_left : ∀ t x, Hinv t (H t x) = x
  inv_right : ∀ t x, H t (Hinv t x) = x
  start : H 0 = id

/-- **Identity ambient isotopy.** The identity ambient isotopy of $\mathbb{R}^3$ has forward
and inverse families $H_t$ and $G_t$ equal to the identity map of $\mathbb{R}^3$ for every
time $t$. -/
def AmbientIsotopy.id : AmbientIsotopy where
  H := fun _ => _root_.id
  Hinv := fun _ => _root_.id
  smooth := by
    have hfun : Function.uncurry (fun _ => _root_.id) =
        (Prod.snd : ℝ × R3 → R3) := by
      funext ⟨t, x⟩
      rfl
    rw [hfun]
    exact contDiff_snd
  smooth_inv := by
    have hfun : Function.uncurry (fun _ => _root_.id) =
        (Prod.snd : ℝ × R3 → R3) := by
      funext ⟨t, x⟩
      rfl
    rw [hfun]
    exact contDiff_snd
  inv_left := fun _ _ => rfl
  inv_right := fun _ _ => rfl
  start := rfl

/-- **Inverse ambient isotopy.** The inverse of an ambient isotopy with forward family $(H_t)$ and
inverse family $(H_t^{-1})$ is the ambient isotopy whose forward family is $(H_t^{-1})$ and whose
inverse family is $(H_t)$; at each time $t$ it is the inverse diffeomorphism of $H_t$. -/
def AmbientIsotopy.symm (Φ : AmbientIsotopy) : AmbientIsotopy where
  H := Φ.Hinv
  Hinv := Φ.H
  smooth := Φ.smooth_inv
  smooth_inv := Φ.smooth
  inv_left := Φ.inv_right
  inv_right := Φ.inv_left
  start := by
    funext x
    have h := Φ.inv_right 0 x
    rw [Φ.start] at h
    exact h

/-- **Composition of ambient isotopies.** If $\Phi$ and $\Psi$ are smooth ambient isotopies of
$\mathbb{R}^3$ with forward families $H_t, H'_t$ and inverse families $G_t, G'_t$, their
composition (first $\Phi$, then $\Psi$, at the same time parameter) is the ambient isotopy
with forward family $H'_t \circ H_t$ and inverse family $G_t \circ G'_t$. -/
def AmbientIsotopy.comp (Φ Ψ : AmbientIsotopy) : AmbientIsotopy where
  H := fun t x => Ψ.H t (Φ.H t x)
  Hinv := fun t x => Φ.Hinv t (Ψ.Hinv t x)
  smooth := by
    have hpre : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × R3 => (p.1, Φ.H p.1 p.2)) :=
      contDiff_fst.prodMk Φ.smooth
    have hfun : Function.uncurry (fun t x => Ψ.H t (Φ.H t x)) =
        fun p : ℝ × R3 => Ψ.H p.1 (Φ.H p.1 p.2) := by
      funext ⟨t, x⟩
      rfl
    rw [hfun]
    exact Ψ.smooth.comp hpre
  smooth_inv := by
    have hpre : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × R3 => (p.1, Ψ.Hinv p.1 p.2)) :=
      contDiff_fst.prodMk Ψ.smooth_inv
    have hfun : Function.uncurry (fun t x => Φ.Hinv t (Ψ.Hinv t x)) =
        fun p : ℝ × R3 => Φ.Hinv p.1 (Ψ.Hinv p.1 p.2) := by
      funext ⟨t, x⟩
      rfl
    rw [hfun]
    exact Φ.smooth_inv.comp hpre
  inv_left := by
    intro t x
    simp [Φ.inv_left, Ψ.inv_left]
  inv_right := by
    intro t x
    simp [Φ.inv_right, Ψ.inv_right]
  start := by
    funext x
    simp [Φ.start, Ψ.start]

/-- **Orientation-preserving reparametrization of the circle.** An orientation-preserving
smooth reparametrization of the circle is given by maps $f, g \colon \mathbb{R} \to \mathbb{R}$,
both $C^\infty$ and inverse to each other ($g(f(t)) = t$ and $f(g(t)) = t$ for all $t$), such
that $f(t + 2\pi) = f(t) + 2\pi$ and $g(t + 2\pi) = g(t) + 2\pi$ for all $t$, and $f$ is
strictly increasing. Here $f$ is a lift of the reparametrization and $g$ is a lift of its
inverse. -/
structure CircleReparam where
  f : ℝ → ℝ
  finv : ℝ → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) f
  smooth_inv : ContDiff ℝ (⊤ : ℕ∞) finv
  left_inv : ∀ t, finv (f t) = t
  right_inv : ∀ t, f (finv t) = t
  periodic : ∀ t, f (t + 2 * Real.pi) = f t + 2 * Real.pi
  periodic_inv : ∀ t, finv (t + 2 * Real.pi) = finv t + 2 * Real.pi
  mono : StrictMono f

/-- **Identity reparametrization of the circle.** The identity circle reparametrization has
lift and inverse lift both equal to the identity map of $\mathbb{R}$. -/
def CircleReparam.id : CircleReparam where
  f := _root_.id
  finv := _root_.id
  smooth := contDiff_id
  smooth_inv := contDiff_id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  periodic := fun _ => rfl
  periodic_inv := fun _ => rfl
  mono := strictMono_id

/-- **Inverse circle reparametrization.** The inverse of a circle reparametrization with lift
$f$ and inverse lift $f^{-1}$ is the circle reparametrization whose lift is $f^{-1}$ and whose
inverse lift is $f$. -/
def CircleReparam.symm (σ : CircleReparam) : CircleReparam where
  f := σ.finv
  finv := σ.f
  smooth := σ.smooth_inv
  smooth_inv := σ.smooth
  left_inv := σ.right_inv
  right_inv := σ.left_inv
  periodic := σ.periodic_inv
  periodic_inv := σ.periodic
  mono := by
    intro a b hab
    by_contra hnot
    have hle : σ.finv b ≤ σ.finv a := le_of_not_gt hnot
    have hmono := σ.mono.monotone hle
    rw [σ.right_inv, σ.right_inv] at hmono
    exact not_lt_of_ge hmono hab

/-- **Composition of circle reparametrizations.** If $\sigma$ and $\tau$ are circle
reparametrizations with lifts $f_\sigma, f_\tau$ and inverse lifts $g_\sigma, g_\tau$, their
composition (first $\sigma$, then $\tau$) is the circle reparametrization with lift
$f_\tau \circ f_\sigma$ and inverse lift $g_\sigma \circ g_\tau$. -/
def CircleReparam.comp (σ τ : CircleReparam) : CircleReparam where
  f := τ.f ∘ σ.f
  finv := σ.finv ∘ τ.finv
  smooth := τ.smooth.comp σ.smooth
  smooth_inv := σ.smooth_inv.comp τ.smooth_inv
  left_inv := by
    intro t
    simp [τ.left_inv, σ.left_inv]
  right_inv := by
    intro t
    simp [σ.right_inv, τ.right_inv]
  periodic := by
    intro t
    simp [σ.periodic, τ.periodic]
  periodic_inv := by
    intro t
    simp [τ.periodic_inv, σ.periodic_inv]
  mono := τ.mono.comp σ.mono

/-- **Isotopy of parametrized knots.** Two parametrized knots $\gamma_1, \gamma_2$ in
$\mathbb{R}^3$ are isotopic (oriented ambient isotopy) if there are a smooth ambient isotopy
of $\mathbb{R}^3$ with forward family $H_t$ and an orientation-preserving reparametrization
of the circle with lift $f$ such that $H_1(\gamma_1(t)) = \gamma_2(f(t))$ for every
$t \in \mathbb{R}$. -/
def ParametrizedKnot.Isotopic (K₁ K₂ : ParametrizedKnot) : Prop :=
  ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
    ∀ t, Φ.H 1 (K₁.curve t) = K₂.curve (σ.f t)

theorem ParametrizedKnot.Isotopic.refl (K : ParametrizedKnot) :
    K.Isotopic K :=
  ⟨AmbientIsotopy.id, CircleReparam.id, fun _ => rfl⟩

theorem ParametrizedKnot.Isotopic.symm {K₁ K₂ : ParametrizedKnot}
    (h : K₁.Isotopic K₂) : K₂.Isotopic K₁ := by
  obtain ⟨Φ, σ, hΦσ⟩ := h
  refine ⟨Φ.symm, σ.symm, fun t => ?_⟩
  have hcongr := congrArg (Φ.Hinv 1) (hΦσ (σ.finv t))
  simpa [AmbientIsotopy.symm, CircleReparam.symm, σ.right_inv,
    Φ.inv_left] using hcongr.symm

theorem ParametrizedKnot.Isotopic.trans {K₁ K₂ K₃ : ParametrizedKnot}
    (h₁₂ : K₁.Isotopic K₂) (h₂₃ : K₂.Isotopic K₃) :
    K₁.Isotopic K₃ := by
  obtain ⟨Φ, σ, hΦσ⟩ := h₁₂
  obtain ⟨Ψ, τ, hΨτ⟩ := h₂₃
  refine ⟨Φ.comp Ψ, σ.comp τ, fun t => ?_⟩
  calc
    (Φ.comp Ψ).H 1 (K₁.curve t) = Ψ.H 1 (Φ.H 1 (K₁.curve t)) := rfl
    _ = Ψ.H 1 (K₂.curve (σ.f t)) := by rw [hΦσ]
    _ = K₃.curve ((σ.comp τ).f t) := hΨτ (σ.f t)

/-- **Isotopy of parametrized links.** Two parametrized links in $\mathbb{R}^3$ with $n$
components $\gamma^1_i$ and $\gamma^2_i$ ($i < n$) are isotopic (oriented, labeled ambient
isotopy) if there are a single smooth ambient isotopy of $\mathbb{R}^3$ with forward family
$H_t$ and, for each $i < n$, an orientation-preserving reparametrization of the circle with
lift $f_i$, such that $H_1(\gamma^1_i(t)) = \gamma^2_i(f_i(t))$ for every $i < n$ and every
$t \in \mathbb{R}$. -/
def ParametrizedLink.Isotopic {n : ℕ}
    (L₁ L₂ : ParametrizedLink n) : Prop :=
  ∃ Φ : AmbientIsotopy, ∃ σ : Fin n → CircleReparam,
    ∀ i t, Φ.H 1 ((L₁.component i).curve t) =
      (L₂.component i).curve ((σ i).f t)

theorem ParametrizedLink.Isotopic.refl {n : ℕ} (L : ParametrizedLink n) :
    L.Isotopic L :=
  ⟨AmbientIsotopy.id, fun _ => CircleReparam.id, fun _ _ => rfl⟩

theorem ParametrizedLink.Isotopic.symm {n : ℕ}
    {L₁ L₂ : ParametrizedLink n} (h : L₁.Isotopic L₂) :
    L₂.Isotopic L₁ := by
  obtain ⟨Φ, σ, hΦσ⟩ := h
  refine ⟨Φ.symm, fun i => (σ i).symm, fun i t => ?_⟩
  have hcongr := congrArg (Φ.Hinv 1) (hΦσ i ((σ i).finv t))
  simpa [AmbientIsotopy.symm, CircleReparam.symm, (σ i).right_inv,
    Φ.inv_left] using hcongr.symm

theorem ParametrizedLink.Isotopic.trans {n : ℕ}
    {L₁ L₂ L₃ : ParametrizedLink n} (h₁₂ : L₁.Isotopic L₂)
    (h₂₃ : L₂.Isotopic L₃) : L₁.Isotopic L₃ := by
  obtain ⟨Φ, σ, hΦσ⟩ := h₁₂
  obtain ⟨Ψ, τ, hΨτ⟩ := h₂₃
  refine ⟨Φ.comp Ψ, fun i => (σ i).comp (τ i), fun i t => ?_⟩
  calc
    (Φ.comp Ψ).H 1 ((L₁.component i).curve t) =
        Ψ.H 1 (Φ.H 1 ((L₁.component i).curve t)) := rfl
    _ = Ψ.H 1 ((L₂.component i).curve ((σ i).f t)) := by rw [hΦσ]
    _ = (L₃.component i).curve (((σ i).comp (τ i)).f t) :=
      hΨτ i ((σ i).f t)

/-- **Trace of a parametrized link.** The trace of a parametrized link $L$ in Euclidean 3-space
is the union of the images of its component curves: the set of all points $\gamma(t)$, where
$\gamma$ is a component of $L$ and $t \in \mathbb{R}$. -/
def ParametrizedLink.trace {n : ℕ} (L : ParametrizedLink n) : Set R3 :=
  ⋃ i, Set.range (L.component i).curve

/-- **Total contour length of a parametrized link.** Let $L$ be a parametrized link in
Euclidean 3-space with components $\gamma_1, \dots, \gamma_n$, each a $2\pi$-periodic curve.
The total contour length of $L$ is the sum over all components $\gamma_i$ of the contour
length of $\gamma_i$ on one period $[0, 2\pi]$. It is a value in $[0, \infty]$. -/
noncomputable def ParametrizedLink.totalContourLength {n : ℕ}
    (L : ParametrizedLink n) : ENNReal :=
  ∑ i, contourLength (L.component i).curve 0 (2 * Real.pi)

/-- **Ropelength ratio of a parametrized link.** For a parametrized link $L$, the ropelength
ratio of $L$ is its total contour length divided by the thickness of its trace (the union of the
images of its components), a value in $[0, \infty]$ computed with the division of $[0, \infty]$. -/
noncomputable def ParametrizedLink.ropelengthRatio {n : ℕ}
    (L : ParametrizedLink n) : ENNReal :=
  L.totalContourLength / thickness L.trace

/-- **Ropelength of a parametrized link.** For a parametrized link $L$ with $n$ components, the
ropelength of $L$ is the infimum, in $[0, \infty]$, of the ropelength ratios of all parametrized
links $L'$ with $n$ components that are isotopic to $L$. It is the ropelength of the oriented,
labeled ambient-isotopy type of $L$. -/
noncomputable def ParametrizedLink.ropelength {n : ℕ}
    (L : ParametrizedLink n) : ENNReal :=
  ⨅ L' : ParametrizedLink n, ⨅ _ : L'.Isotopic L, L'.ropelengthRatio

/-- **Ropelength is at most the ratio of any isotopic link.** Let $L$ and $L'$ be parametrized
links with $n$ components. If $L'$ is isotopic to $L$, then the ropelength of $L$ is at most
the ropelength ratio of $L'$. -/
theorem ParametrizedLink.ropelength_le_ratio_of_isotopic {n : ℕ}
    {L L' : ParametrizedLink n} (h : L'.Isotopic L) :
    L.ropelength ≤ L'.ropelengthRatio :=
  iInf₂_le L' h

/-- **Ropelength is at most the ropelength ratio.** For every parametrized link $L$ with $n$
components, the ropelength of $L$ is at most the ropelength ratio of $L$. -/
theorem ParametrizedLink.ropelength_le_ratio_self {n : ℕ}
    (L : ParametrizedLink n) : L.ropelength ≤ L.ropelengthRatio :=
  L.ropelength_le_ratio_of_isotopic (ParametrizedLink.Isotopic.refl L)

/-- **Ropelength is an isotopy invariant.** Let $L_1$ and $L_2$ be parametrized links with $n$
components. If $L_1$ is isotopic to $L_2$ (by an oriented, labeled ambient isotopy), then the
ropelength of $L_1$ equals the ropelength of $L_2$. -/
theorem ParametrizedLink.ropelength_eq_of_isotopic {n : ℕ}
    {L₁ L₂ : ParametrizedLink n} (h : L₁.Isotopic L₂) :
    L₁.ropelength = L₂.ropelength := by
  apply le_antisymm
  · apply le_iInf₂
    intro L' h'
    exact ParametrizedLink.ropelength_le_ratio_of_isotopic (h'.trans h.symm)
  · apply le_iInf₂
    intro L' h'
    exact ParametrizedLink.ropelength_le_ratio_of_isotopic (h'.trans h)

/-- **Parametrized knot as a one-component link.** A parametrized knot $K$ determines the
parametrized link with one component, whose single component is $K$; the pairwise disjointness
condition holds trivially. -/
def ParametrizedKnot.toLink (K : ParametrizedKnot) : ParametrizedLink 1 where
  component := fun _ => K
  pairwiseDisjoint := by
    intro i _ j _ hij
    exact (hij (Subsingleton.elim i j)).elim

/-- **Isotopic knots give isotopic one-component links.** If $K_1$ and $K_2$ are parametrized
knots and $K_1$ is isotopic to $K_2$, then the one-component parametrized link of $K_1$ is
isotopic to the one-component parametrized link of $K_2$. -/
theorem ParametrizedKnot.Isotopic.toLink {K₁ K₂ : ParametrizedKnot}
    (h : K₁.Isotopic K₂) : K₁.toLink.Isotopic K₂.toLink := by
  obtain ⟨Φ, σ, hΦσ⟩ := h
  exact ⟨Φ, fun _ => σ, fun _ t => hΦσ t⟩

@[simp]
theorem ParametrizedKnot.trace_toLink (K : ParametrizedKnot) :
    K.toLink.trace = Set.range K.curve := by
  ext x
  simp [ParametrizedLink.trace, ParametrizedKnot.toLink]

@[simp]
theorem ParametrizedKnot.totalContourLength_toLink (K : ParametrizedKnot) :
    K.toLink.totalContourLength =
      contourLength K.curve 0 (2 * Real.pi) := by
  simp [ParametrizedLink.totalContourLength, ParametrizedKnot.toLink]

/-- **Ropelength of a parametrized knot.** The ropelength of a parametrized knot $K$ is the
ropelength of the one-component parametrized link determined by $K$: the infimum, in
$[0, \infty]$, of the ropelength ratios of all one-component parametrized links that are
isotopic to the one-component link of $K$. -/
noncomputable def ParametrizedKnot.ropelength (K : ParametrizedKnot) :
    ENNReal :=
  K.toLink.ropelength

end MathlibExt.Topology.Knot.Euclidean
