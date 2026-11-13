/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Surface subgroups of finite-covolume Kleinian groups (Reid, Question 2.1)

B. Farb (ed.), Problems on Mapping Class Groups and Related Topics, Ch. 17 (A. W. Reid), Question
2.1: let `M = H³/Γ` be a finite volume hyperbolic `3`-manifold; does `Γ` contain a surface subgroup?
(Answered for non-compact `M` by Cooper–Long–Reid; the closed case remained.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.Topology.Algebra.Group.Matrix

@[expose] public section

namespace MathlibExt.GroupTheory.KleinianLatticeSurfaceSubgroupAMR109Problem0244Wanted

/-!
Source: B. Farb (ed.), Problems on Mapping Class Groups and Related Topics (2006), Ch. 17 (A. W.
Reid), Question 2.1. UnsolvedMath record UM-11000244 (`AMR-109-0244`), dataset ulamai/UnsolvedMath
v1.8.0.

`M = H³/Γ` with `Γ ≤ PSL(2, ℂ)` discrete and torsion-free (so `M` is a manifold); finite volume is
finite covolume: some measurable fundamental domain of the left action of `Γ` on `PSL(2, ℂ)` has
finite Haar measure, for a Haar measure on the Borel `σ`-algebra (`PSL(2, ℂ)/PSU(2) = H³` with
`PSU(2)` compact, so this is the finiteness of the hyperbolic volume). A surface subgroup is a
subgroup isomorphic to the fundamental group `⟨a₁, b₁, …, a_g, b_g | ∏ [aᵢ, bᵢ]⟩` of a closed
orientable surface of genus `g ≥ 2`, stated as an injective homomorphism into `Γ`.
-/

/-- `PSL(2, ℂ)`, with the quotient topology from `SL(2, ℂ)`. -/
abbrev PSL2C : Type :=
  Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ

/-- The relator `∏_{i < g} [aᵢ, bᵢ]` of the fundamental group of the closed orientable surface of
genus `g`; `Sum.inl i` is `aᵢ` and `Sum.inr i` is `bᵢ`. -/
def surfaceRelator (g : ℕ) : FreeGroup (Fin g ⊕ Fin g) :=
  (List.ofFn fun i : Fin g => FreeGroup.of (Sum.inl i) * FreeGroup.of (Sum.inr i) *
    (FreeGroup.of (Sum.inl i))⁻¹ * (FreeGroup.of (Sum.inr i))⁻¹).prod

/-- The fundamental group of the closed orientable surface of genus `g`. -/
abbrev SurfaceGroup (g : ℕ) : Type :=
  PresentedGroup ({surfaceRelator g} : Set (FreeGroup (Fin g ⊕ Fin g)))

/-- Reid's Question 2.1 (Farb (ed.), Problems on Mapping Class Groups, Ch. 17): if `M = H³ / Γ` is
a finite-volume hyperbolic `3`-manifold, i.e. `Γ ≤ PSL(2, ℂ)` is discrete, torsion-free and of
finite covolume (a measurable fundamental domain of finite Haar measure for the left action of `Γ`),
then `Γ` contains the fundamental group of a closed orientable surface of genus at least `2`. -/
def kleinianLatticeContainsSurfaceGroup : Prop :=
  ∀ Γ : Subgroup PSL2C, DiscreteTopology Γ → (∀ γ ∈ Γ, γ ≠ 1 → ¬ IsOfFinOrder γ) →
    ∀ [MeasurableSpace PSL2C] [BorelSpace PSL2C] (μ : MeasureTheory.Measure PSL2C)
      [μ.IsHaarMeasure],
      (∃ F : Set PSL2C, MeasurableSet F ∧ MeasureTheory.IsFundamentalDomain Γ F μ ∧ μ F < ⊤) →
      ∃ g : ℕ, 2 ≤ g ∧ ∃ φ : SurfaceGroup g →* Γ, Function.Injective φ

/--
Resolved true: every torsion-free lattice in `PSL(2, ℂ)` contains a closed surface group of genus at
least `2`: Cooper–Long–Reid for non-compact finite-volume quotients (Theorem 1.1, applied to the
compact core, whose boundary tori are incompressible; Reid's chapter records this case as answered)
and Kahn–Markovic for closed hyperbolic `3`-manifolds (Theorem 1.1: a quasi-Fuchsian closed surface
subgroup). Source: B. Farb (ed.), Problems on Mapping Class Groups and Related Topics (2006), Ch. 17
(A. W. Reid), Question 2.1; resolution: J. Kahn and V. Markovic, Immersing almost geodesic surfaces
in a closed hyperbolic three manifold, Ann. of Math. (2) 175 (2012), 1127-1190, arXiv:0910.5501
(closed case); D. Cooper, D. D. Long and A. W. Reid, Essential closed surfaces in bounded
3-manifolds, J. Amer. Math. Soc. 10 (1997), 553-563 (non-compact case, reference [8] of Reid's
chapter), Kahn-Markovic Theorem 1.1: for a closed hyperbolic 3-manifold M = H³/Γ, Γ contains a
quasi-Fuchsian conjugate g F g⁻¹ of a Fuchsian group F uniformizing a closed Riemann surface H²/F
(genus ≥ 2: the Remark after it gives H²/F a pants decomposition); Theorem 1.2: a closed surface S
with a π₁-injective map S → M; Cooper-Long-Reid Theorem 1.1: a compact 3-manifold with nonempty
incompressible boundary whose interior has a complete hyperbolic structure is covered by a product F
× I or contains an essential (π₁-injective, non-peripheral) closed surface of genus at least 2;
Reid's chapter after Question 2.1: "This was answered in [8] for non-compact but finite volume
manifolds", https://arxiv.org/abs/0910.5501.
-/
public theorem_wanted kleinianLatticeContainsSurfaceGroup_holds :
    kleinianLatticeContainsSurfaceGroup

end MathlibExt.GroupTheory.KleinianLatticeSurfaceSubgroupAMR109Problem0244Wanted
