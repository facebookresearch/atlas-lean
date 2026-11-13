/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Unbounded fragmentation norm on Diff₀(T²) (Oberwolfach Report 33/2006)

D. Burago (joint work with S. Ivanov and L. Polterovich), Quasi-norms on groups of geometric origin,
Oberwolfach Report 33/2006, pp. 2022-2023, Definition 4 and Open Problems: a diffeomorphism is
elementary if its support lies in some disc; does there exist a constant `C` such that every
diffeomorphism of the two-dimensional torus isotopic to the identity is a product of no more than
`C` elementary diffeomorphisms, i.e. is `L` bounded on `Diff₀(T²)`? What about the compactly
supported diffeomorphisms of the open Möbius strip?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.Sheaf.Basic

@[expose] public section

namespace MathlibExt.Topology.TorusFragmentationNormOWR1319Problem008Wanted

/-!
Source: D. Burago (joint work with S. Ivanov and L. Polterovich), Quasi-norms on groups of geometric
origin, in Geometric Group Theory, Hyperbolic Dynamics and Symplectic Geometry, Oberwolfach Reports
3 (2006), no. 33, pp. 2022-2023, Definition 4 and Open Problems, DOI 10.4171/OWR/2006/33.
UnsolvedMath record UM-30000540 (`OWR-1319-008`), dataset ulamai/UnsolvedMath v1.8.0.

The torus is `Circle × Circle` with Mathlib's smooth structure (model `(𝓡 1).prod (𝓡 1)`);
diffeomorphisms are `C^∞` (`Diffeomorph ... ∞`). A disc is an open set `U` diffeomorphic to the open
unit ball of `ℝ²` (the report's `φ : Bⁿ → D`; Bowden-Hensel-Webb's `supp(hᵢ) ⊂ Uᵢ ≅ Bⁿ`), and the
support of `h` is the closure of `{x | h x ≠ x}`. Isotopic to the identity means smoothly isotopic:
a smooth `H : ℝ × T² → T²` through diffeomorphisms from the identity (`t = 0`) to `f` (`t = 1`),
i.e. `f ∈ Diff₀(T²)`. The second question (the open Möbius strip `ℝ²#ℝP²`) is not formalized: it is
not answered by the resolving paper, and Mathlib has no smooth structure on the open Möbius strip
(no quotient or non-orientable surface constructions).
-/

open scoped Manifold ContDiff

/-- The model with corners of the two-torus `Circle × Circle`: the product of two copies of the
model `𝓡 1` of Mathlib's smooth circle. -/
noncomputable abbrev torusModel :=
  (𝓡 1).prod (𝓡 1)

/-- The open unit ball of `ℝ²`, an open subset and hence a smooth manifold modelled on `𝓡 2`. -/
def unitBall : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2)) :=
  ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

/-- A diffeomorphism `h` of the torus is elementary (Burago-Ivanov-Polterovich, Definition 4;
Bowden-Hensel-Webb, Definition 2.3) if its support, the closure of `{x | h x ≠ x}`, lies in an
open subset `U` of the torus that is diffeomorphic to the open unit ball of `ℝ²` (a disc). -/
def IsElementary (h : Diffeomorph torusModel torusModel (Circle × Circle) (Circle × Circle) ∞) :
    Prop :=
  ∃ U : TopologicalSpace.Opens (Circle × Circle),
    Nonempty (Diffeomorph torusModel (𝓡 2) U unitBall ∞) ∧
      closure {x | h x ≠ x} ⊆ (U : Set (Circle × Circle))

/-- A diffeomorphism `f` of the torus is (smoothly) isotopic to the identity: there is a smooth map
`H : ℝ × T² → T²` with `H (0, ·) = id`, `H (1, ·) = f` and every `H (t, ·)` a diffeomorphism. -/
def IsIsotopicToId (f : Diffeomorph torusModel torusModel (Circle × Circle) (Circle × Circle) ∞) :
    Prop :=
  ∃ H : ℝ × (Circle × Circle) → Circle × Circle,
    ContMDiff (𝓘(ℝ).prod torusModel) torusModel ∞ H ∧ (∀ x, H (0, x) = x) ∧
      (∀ x, H (1, x) = f x) ∧
      ∀ t : ℝ, ∃ g : Diffeomorph torusModel torusModel (Circle × Circle) (Circle × Circle) ∞,
        ∀ x, g x = H (t, x)

/-- `f` is a product `h₁ ∘ ⋯ ∘ h_k` of at most `C` elementary diffeomorphisms. -/
def IsProductOfElementary
    (f : Diffeomorph torusModel torusModel (Circle × Circle) (Circle × Circle) ∞) (C : ℕ) : Prop :=
  ∃ l : List (Diffeomorph torusModel torusModel (Circle × Circle) (Circle × Circle) ∞),
    l.length ≤ C ∧ (∀ h ∈ l, IsElementary h) ∧ (⇑f = (l.map (⇑)).foldr (· ∘ ·) id)

/-- The torus question of Burago, Ivanov and Polterovich: there is a constant `C` such that every
diffeomorphism of the two-torus isotopic to the identity is a product of at most `C` elementary
diffeomorphisms (diffeomorphisms supported in discs), i.e. the fragmentation norm is bounded on
`Diff₀(T²)`. -/
def torusFragmentationBounded : Prop :=
  ∃ C : ℕ, ∀ f : Diffeomorph torusModel torusModel (Circle × Circle) (Circle × Circle) ∞,
    IsIsotopicToId f → IsProductOfElementary f C

/--
Resolved false: Bowden, Hensel and Webb prove that for every genus `g ≥ 1` the identity component
`Diff₀(S_g)` of the diffeomorphism group of the closed oriented surface `S_g` is not uniformly
perfect and has unbounded fragmentation norm `‖f‖_Frag = min {N | f = h₁ ⋯ h_N, supp(hᵢ) ⊂ Uᵢ ≅
Bⁿ}`, answering the question of Burago, Ivanov and Polterovich; the torus is the case `g = 1`, so no
constant `C` works. Source: D. Burago (joint work with S. Ivanov and L. Polterovich), Quasi-norms on
groups of geometric origin, in Geometric Group Theory, Hyperbolic Dynamics and Symplectic Geometry,
Oberwolfach Reports 3 (2006), no. 33, pp. 2022-2023, Definition 4 and Open Problems, DOI
10.4171/OWR/2006/33; resolution: J. Bowden, S. Hensel and R. Webb, Quasi-morphisms on surface
diffeomorphism groups, J. Amer. Math. Soc. 35 (2022), 211-231, DOI 10.1090/jams/981,
arXiv:1909.07164, Corollary 1.3 (= Corollary 5.2): for g ≥ 1 the group Diff₀(S_g) is not uniformly
perfect and has unbounded fragmentation norm; Definition 2.3 (fragmentation norm); Section 5.2 (the
torus), https://arxiv.org/abs/1909.07164.
-/
public theorem_wanted torusFragmentationBounded_refuted : ¬ torusFragmentationBounded

end MathlibExt.Topology.TorusFragmentationNormOWR1319Problem008Wanted
