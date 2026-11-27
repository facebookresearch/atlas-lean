/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation
public import MathlibExt.Topology.Knot.EuclideanLink
public import MathlibExt.Topology.ConwayKnotShared

import Mathlib.Tactic.FinCases

/-!
# The Conway knot definitions and the Euclidean link API

`knotEquiv` identifies the lean-eval knot type in `MathlibExt.Topology.ConwayKnotShared`
with the parametrized knots of `MathlibExt.Topology.Knot.EuclideanLink`.
`knot_isotopic_iff` and `twoLink_isotopic_iff` transfer ambient isotopy in both directions,
preserving the component labels of two-component links.
-/

@[expose] public section

namespace MathlibExt.Topology.ConwayKnotEuclideanBridge

/-- **Knots as parametrized knots.** A knot in $\mathbb{R}^3$, given by a smooth $2\pi$-periodic
immersion $\gamma : \mathbb{R} \to \mathbb{R}^3$ that is injective on $[0, 2\pi)$, is sent to the
parametrized knot with the same parametrization $\gamma$. -/
def toParametrizedKnot (K : ConwayKnotShared.KnotTheory.Knot) :
    Knot.Euclidean.ParametrizedKnot where
  curve := K.curve
  smooth := K.smooth
  periodic := K.periodic
  injOn := K.injOn
  immersion := K.immersion

/-- **Parametrized knots as knots.** A parametrized knot in $\mathbb{R}^3$, given by a smooth
$2\pi$-periodic immersion $\gamma : \mathbb{R} \to \mathbb{R}^3$ that is injective on
$[0, 2\pi)$, is sent to the knot with the same parametrization $\gamma$. -/
def ofParametrizedKnot (K : Knot.Euclidean.ParametrizedKnot) :
    ConwayKnotShared.KnotTheory.Knot where
  curve := K.curve
  smooth := K.smooth
  periodic := K.periodic
  injOn := K.injOn
  immersion := K.immersion

@[simp]
theorem ofParametrizedKnot_toParametrizedKnot
    (K : ConwayKnotShared.KnotTheory.Knot) :
    ofParametrizedKnot (toParametrizedKnot K) = K := by
  cases K
  rfl

@[simp]
theorem toParametrizedKnot_ofParametrizedKnot
    (K : Knot.Euclidean.ParametrizedKnot) :
    toParametrizedKnot (ofParametrizedKnot K) = K := by
  cases K
  rfl

/-- **Knots are the same as parametrized knots.** Sending a knot in $\mathbb{R}^3$ to the
parametrized knot with the same parametrization is a bijection from knots to parametrized knots,
whose inverse sends a parametrized knot to the knot with the same parametrization. -/
def knotEquiv :
    ConwayKnotShared.KnotTheory.Knot ≃ Knot.Euclidean.ParametrizedKnot where
  toFun := toParametrizedKnot
  invFun := ofParametrizedKnot
  left_inv := ofParametrizedKnot_toParametrizedKnot
  right_inv := toParametrizedKnot_ofParametrizedKnot

/-- **Conway-knot ambient isotopies as Euclidean ambient isotopies.** An ambient isotopy of
$\mathbb{R}^3$ in the sense of the Conway knot statements, given by maps
$H_t : \mathbb{R}^3 \to \mathbb{R}^3$ for $t \in \mathbb{R}$ with $(t, x) \mapsto H_t(x)$ smooth
and $H_0 = \mathrm{id}$, and maps $G_t : \mathbb{R}^3 \to \mathbb{R}^3$ with
$(t, x) \mapsto G_t(x)$ smooth and $G_t \circ H_t = H_t \circ G_t = \mathrm{id}$ for every $t$,
is sent to the smooth ambient isotopy of Euclidean 3-space, in the sense of parametrized links,
with the same forward family $H$ and inverse family $G$. -/
def toEuclideanAmbientIsotopy
    (Φ : ConwayKnotShared.KnotTheory.AmbientIsotopy) :
    Knot.Euclidean.AmbientIsotopy where
  H := Φ.H
  Hinv := Φ.Hinv
  smooth := Φ.smooth
  smooth_inv := Φ.smooth_inv
  inv_left := Φ.inv_left
  inv_right := Φ.inv_right
  start := Φ.start

/-- **Euclidean ambient isotopies as Conway-knot ambient isotopies.** A smooth ambient isotopy
of Euclidean 3-space in the sense of parametrized links, given by maps
$H_t : \mathbb{R}^3 \to \mathbb{R}^3$ for $t \in \mathbb{R}$ with $(t, x) \mapsto H_t(x)$ smooth
and $H_0 = \mathrm{id}$, and maps $G_t : \mathbb{R}^3 \to \mathbb{R}^3$ with
$(t, x) \mapsto G_t(x)$ smooth and $G_t \circ H_t = H_t \circ G_t = \mathrm{id}$ for every $t$,
is sent to the ambient isotopy of $\mathbb{R}^3$ in the sense of the Conway knot statements with
the same forward family $H$ and inverse family $G$. -/
def ofEuclideanAmbientIsotopy (Φ : Knot.Euclidean.AmbientIsotopy) :
    ConwayKnotShared.KnotTheory.AmbientIsotopy where
  H := Φ.H
  Hinv := Φ.Hinv
  smooth := Φ.smooth
  smooth_inv := Φ.smooth_inv
  inv_left := Φ.inv_left
  inv_right := Φ.inv_right
  start := Φ.start

/-- **Conway-knot circle reparametrizations as Euclidean ones.** An orientation-preserving smooth
reparametrization of the circle in the sense of the Conway knot statements, given by a smooth
strictly increasing map $f : \mathbb{R} \to \mathbb{R}$ with smooth two-sided inverse $g$ such that
$f(t + 2\pi) = f(t) + 2\pi$ and $g(t + 2\pi) = g(t) + 2\pi$ for all $t$, is sent to the circle
reparametrization, in the sense of parametrized links, with the same lift $f$ and inverse
lift $g$. -/
def toEuclideanCircleReparam
    (σ : ConwayKnotShared.KnotTheory.CircleReparam) :
    Knot.Euclidean.CircleReparam where
  f := σ.f
  finv := σ.finv
  smooth := σ.smooth
  smooth_inv := σ.smooth_inv
  left_inv := σ.left_inv
  right_inv := σ.right_inv
  periodic := σ.periodic
  periodic_inv := σ.periodic_inv
  mono := σ.mono

/-- **Euclidean circle reparametrizations as Conway-knot ones.** A circle reparametrization in
the sense of parametrized links, given by a smooth strictly increasing map
$f : \mathbb{R} \to \mathbb{R}$ with smooth two-sided inverse $g$ such that
$f(t + 2\pi) = f(t) + 2\pi$ and $g(t + 2\pi) = g(t) + 2\pi$ for all $t$, is sent to the
orientation-preserving smooth reparametrization of the circle in the sense of the Conway knot
statements with the same lift $f$ and inverse lift $g$. -/
def ofEuclideanCircleReparam (σ : Knot.Euclidean.CircleReparam) :
    ConwayKnotShared.KnotTheory.CircleReparam where
  f := σ.f
  finv := σ.finv
  smooth := σ.smooth
  smooth_inv := σ.smooth_inv
  left_inv := σ.left_inv
  right_inv := σ.right_inv
  periodic := σ.periodic
  periodic_inv := σ.periodic_inv
  mono := σ.mono

/-- **Isotopy of knots agrees with isotopy of parametrized knots.** For all knots $K_1$ and
$K_2$ in $\mathbb{R}^3$, $K_1$ and $K_2$ are ambient isotopic if and only if the parametrized knots
with the same parametrizations as $K_1$ and $K_2$ are ambient isotopic as parametrized knots. -/
theorem knot_isotopic_iff {K₁ K₂ : ConwayKnotShared.KnotTheory.Knot} :
    ConwayKnotShared.KnotTheory.Knot.Isotopic K₁ K₂ ↔
      Knot.Euclidean.ParametrizedKnot.Isotopic
        (toParametrizedKnot K₁) (toParametrizedKnot K₂) := by
  constructor
  · rintro ⟨Φ, σ, h⟩
    exact ⟨toEuclideanAmbientIsotopy Φ, toEuclideanCircleReparam σ, h⟩
  · rintro ⟨Φ, σ, h⟩
    exact ⟨ofEuclideanAmbientIsotopy Φ, ofEuclideanCircleReparam σ, h⟩

/-- **Two-component links as labeled links.** A two-component link in $\mathbb{R}^3$ with first
component $K$ and second component $L$ is sent to the labeled parametrized link with two
components whose component $0$ is the parametrized knot with the same parametrization as $K$ and
whose component $1$ is the parametrized knot with the same parametrization as $L$. -/
def toParametrizedLink (L : ConwayKnotShared.KnotTheory.TwoLink) :
    Knot.Euclidean.ParametrizedLink 2 where
  component := ![toParametrizedKnot L.K, toParametrizedKnot L.L]
  pairwiseDisjoint := by
    intro i _ j _ hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact L.disjoint
    · exact L.disjoint.symm
    · exact absurd rfl hij

/-- **Labeled two-component links as two-component links.** A labeled parametrized link with
two components $0$ and $1$ is sent to the two-component link in $\mathbb{R}^3$ whose first
component is the knot with the same parametrization as component $0$ and whose second component
is the knot with the same parametrization as component $1$. -/
def ofParametrizedLink (L : Knot.Euclidean.ParametrizedLink 2) :
    ConwayKnotShared.KnotTheory.TwoLink where
  K := ofParametrizedKnot (L.component 0)
  L := ofParametrizedKnot (L.component 1)
  disjoint := by
    have h := L.pairwiseDisjoint (Set.mem_univ 0) (Set.mem_univ 1)
      (by decide : (0 : Fin 2) ≠ 1)
    exact h

@[simp]
theorem ofParametrizedLink_toParametrizedLink
    (L : ConwayKnotShared.KnotTheory.TwoLink) :
    ofParametrizedLink (toParametrizedLink L) = L := by
  cases L
  rfl

/-- **Two-component link isotopy agrees with labeled link isotopy.** Let $L_1$ and $L_2$ be
oriented two-component smooth links in $\mathbb{R}^3$, and regard each as an oriented labeled
smooth link with two components, whose component $0$ is its first component and whose
component $1$ is its second. Then $L_1$ and $L_2$ are ambient isotopic, meaning that a single
smooth ambient isotopy carries each component of $L_1$ onto the corresponding component of
$L_2$ up to orientation-preserving reparametrizations of the circle, if and only if the
associated labeled links are ambient isotopic. -/
theorem twoLink_isotopic_iff
    {L₁ L₂ : ConwayKnotShared.KnotTheory.TwoLink} :
    ConwayKnotShared.KnotTheory.TwoLink.Isotopic L₁ L₂ ↔
      Knot.Euclidean.ParametrizedLink.Isotopic
        (toParametrizedLink L₁) (toParametrizedLink L₂) := by
  constructor
  · rintro ⟨Φ, σ, τ, hK, hL⟩
    refine ⟨toEuclideanAmbientIsotopy Φ,
      ![toEuclideanCircleReparam σ, toEuclideanCircleReparam τ],
      fun i t => ?_⟩
    fin_cases i
    · exact hK t
    · exact hL t
  · rintro ⟨Φ, σ, h⟩
    refine ⟨ofEuclideanAmbientIsotopy Φ,
      ofEuclideanCircleReparam (σ 0), ofEuclideanCircleReparam (σ 1),
      fun t => ?_, fun t => ?_⟩
    · exact h 0 t
    · exact h 1 t

end MathlibExt.Topology.ConwayKnotEuclideanBridge
