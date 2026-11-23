/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Not every Riemannian metric admits a dually flat structure (Amari, FMU list 1(c))

H. Furuhata, H. Matsuzoe and H. Urakawa, Open problems in affine differential geometry and related
topics, Interdiscip. Inform. Sci. 4 (1998), item 1(c) (S. Amari): given a Riemannian manifold `(M,
g)`, can one always introduce a symmetric `(0,3)`-tensor `T` so that `(M, g, ∇, ∇*)` is dually flat?
If the construction is not unique, characterize the class of resulting spaces.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

namespace MathlibExt.Geometry.DuallyFlatStructureAMR59Problem0003Wanted

/-!
Source: H. Furuhata, H. Matsuzoe and H. Urakawa, Open problems in affine differential geometry and
related topics, Interdiscip. Inform. Sci. 4 (1998), no. 2, item 1(c) (S. Amari). UnsolvedMath record
UM-06000003 (`AMR-059-0003`), dataset ulamai/UnsolvedMath v1.8.0.

Only the first question is formalized; the second (characterize the class of resulting spaces) is
open-ended. The question is stated for Riemannian metrics on open subsets `U` of `ℝⁿ` in
coordinates: `g` has smooth entries and is positive definite on `U`, `T` is a smooth totally
symmetric `(0,3)`-tensor on `U`, `∇` and `∇*` are the connections with coefficients `Γᵏᵢⱼ ∓ ½ gᵏˡ
Tᵢⱼₗ` (Levi-Civita `Γᵏᵢⱼ`, Amari's `α = ±1` connections, which are torsion-free and `g`-dual), and
dually flat means both have vanishing curvature `Rˡₖᵢⱼ`. Open subsets of `ℝⁿ` with such a metric are
Riemannian manifolds, so this restricts the claim and its refutation answers the question;
Amari–Armstrong read the question as local and state the negative answer locally.
-/

open scoped ContDiff

/-- The partial derivative `∂ᵢ f(x)` of a real function on `ℝⁿ`. -/
noncomputable def partialDeriv {n : ℕ} (i : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- The Christoffel symbols `Γᵏᵢⱼ = ½ gᵏˡ (∂ᵢ gⱼₗ + ∂ⱼ gᵢₗ - ∂ₗ gᵢⱼ)` of the Levi-Civita connection
of a metric `g` on an open subset of `ℝⁿ` (`gᵏˡ` the inverse matrix). -/
noncomputable def christoffel {n : ℕ} (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (k i j : Fin n) : ℝ :=
  (1 / 2) * ∑ l, (g x)⁻¹ k l * (partialDeriv i (fun y => g y j l) x +
    partialDeriv j (fun y => g y i l) x - partialDeriv l (fun y => g y i j) x)

/-- The coefficients `Γᵏᵢⱼ + (s/2) gᵏˡ Tᵢⱼₗ` of the connection obtained from the Levi-Civita
connection of `g` and the `(0,3)`-tensor `T`: `s = -1` gives `∇` and `s = 1` its `g`-dual `∇*`. -/
noncomputable def shiftedConnection {n : ℕ} (s : ℝ) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (T : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ) (x : Fin n → ℝ) (k i j : Fin n) : ℝ :=
  christoffel g x k i j + s / 2 * ∑ l, (g x)⁻¹ k l * T x i j l

/-- The curvature `Rˡₖᵢⱼ = ∂ᵢ Γˡⱼₖ - ∂ⱼ Γˡᵢₖ + Γᵐⱼₖ Γˡᵢₘ - Γᵐᵢₖ Γˡⱼₘ` of the connection with
coefficients `Γ x l i j = Γˡᵢⱼ` (`∇_{∂ᵢ} ∂ⱼ = Γˡᵢⱼ ∂ₗ`), i.e. `R(∂ᵢ, ∂ⱼ) ∂ₖ = Rˡₖᵢⱼ ∂ₗ`. -/
noncomputable def curvature {n : ℕ} (Γ : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (l k i j : Fin n) : ℝ :=
  partialDeriv i (fun y => Γ y l j k) x - partialDeriv j (fun y => Γ y l i k) x +
    ∑ m, (Γ x m j k * Γ x l i m - Γ x m i k * Γ x l j m)

/-- Amari's question (first part), for Riemannian metrics on open subsets of `ℝⁿ`: every smooth
Riemannian metric `g` (smooth entries, positive definite) admits a smooth totally symmetric
`(0,3)`-tensor `T` such that
`(g, ∇, ∇*)` is dually flat, i.e. both `∇ = ∇^{LC} - ½ g⁻¹T` and its dual `∇* = ∇^{LC} + ½ g⁻¹T`
have vanishing curvature. -/
def everyMetricAdmitsDuallyFlatStructure : Prop :=
  ∀ (n : ℕ) (U : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ),
    IsOpen U → (∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U) → (∀ x ∈ U, (g x).PosDef) →
      ∃ T : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ,
        (∀ i j k, ContDiffOn ℝ ∞ (fun y => T y i j k) U) ∧
        (∀ x i j k, T x i j k = T x j i k ∧ T x i j k = T x i k j) ∧
        ∀ x ∈ U, ∀ l k i j, curvature (shiftedConnection (-1) g T) x l k i j = 0 ∧
          curvature (shiftedConnection 1 g T) x l k i j = 0

/--
Resolved false: by Amari–Armstrong's Theorem 1 a generic Riemannian metric in dimension `n > 3`
admits no compatible dually flat structure even locally, so some smooth metric on an open subset of
`ℝⁿ` admits no such `T`. Source: H. Furuhata, H. Matsuzoe and H. Urakawa, Open problems in affine
differential geometry and related topics, Interdiscip. Inform. Sci. 4 (1998), no. 2, item 1(c) (S.
Amari); resolution: S. Amari and J. Armstrong, Curvature of Hessian manifolds, Differential Geom.
Appl. 33 (2014), 1-12, DOI 10.1016/j.difgeo.2014.01.001, arXiv:1312.1103, §1: Problem 1 (raised in
[FMU99, AN00]): does every Riemannian manifold admit a dually flat structure, a pair of g-dual flat
torsion-free connections? 'We interpret these questions as being essentially local'; 'the answer to
Problem 1 is positive in dimension 2 and negative in dimensions greater than 2'; §2 Theorem 1: a
generic Riemannian metric in dimension n > 3 (the abstract and the counting argument give n > 2)
does not admit a compatible dually flat structure, even locally, https://arxiv.org/abs/1312.1103.
-/
public theorem_wanted everyMetricAdmitsDuallyFlatStructure_refuted :
    ¬ everyMetricAdmitsDuallyFlatStructure

end MathlibExt.Geometry.DuallyFlatStructureAMR59Problem0003Wanted
