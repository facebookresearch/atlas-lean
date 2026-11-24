/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.LinearAlgebra.HermitianFlags
public import MathlibExt.AlgebraicGeometry.BettiFunctoriality
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
/-!
# Actual regular type A1 Grothendieck--Steinberg geometry

The base is the actual open locus of complex 2×2 matrices with nonzero
characteristic discriminant. The spectral cover is the quadratic
characteristic-root incidence. Its other-eigenvalue deck homeomorphism,
absence of fixed points, nonempty fibres and two-graph Steinberg decomposition
are proved. The finite Steinberg convolution sums over those two actual
fibre points; its reflection kernel squares to the diagonal kernel.

The Grothendieck eigenline incidence uses actual Hermitian rank-one flag
projectors satisfying A P = λ P, for arbitrary regular-semisimple A.
The normalized inverse formula first forms the algebraic spectral idempotent
Q and then the Hermitian eigenline projector Q Q* / tr(Q Q*). The matrix A
may be non-normal; its eigenline projector is the Hermitian object.

The coefficient sheaf and bounded-below derived direct image are actual
rational-sheaf pushforwards. The deck endomorphism uses the actual normalized
coefficient-unit map and the literal equality of composite pushforwards.
No full nilpotent Springer, perverse extension or Satake theory is asserted.

Reference: Chriss--Ginzburg, *Representation Theory and Complex Geometry*,
Chapter 3, Grothendieck resolution and regular Weyl/Steinberg correspondences.
V. Ginzburg, https://arxiv.org/abs/math/9802004v3, §9, Proposition 9.3,
printed pp.34--35, supplies the regular Grothendieck/Weyl-cover statement.
Mathlib characteristic polynomials, algebraic closedness and quadratic-root
primitives are reused and not requested as new statements.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.RegularGrothendieckSteinberg
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MathlibExt.LinearAlgebra.HermitianFlags
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.BettiRealization
open MathlibExt.AlgebraicGeometry.BettiFunctoriality
attribute [local instance] HasDerivedCategory.standard
open scoped BigOperators

def discriminant (A : Mat 2) : ℂ := A.trace ^ 2 - 4 * A.det
abbrev RegularMatrix := {A : Mat 2 // discriminant A ≠ 0}
abbrev regularSpace : TopCat.{0} := TopCat.of RegularMatrix

def quadratic (A : Mat 2) (z : ℂ) := z ^ 2 - A.trace * z + A.det

theorem determinant_quadratic (A : Mat 2) (z : ℂ) :
    (A - z • (1 : Mat 2)).det = quadratic A z := by
  simp only [Matrix.det_fin_two, Matrix.trace, Fin.sum_univ_two, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.diag, Fin.isValue,
    (show (0 : Fin 2) ≠ 1 from by decide), (show (1 : Fin 2) ≠ 0 from by decide),
    ite_true, ite_false,
    smul_eq_mul, mul_one, mul_zero, sub_zero, quadratic]
  ring

theorem quadratic_charpoly (A : Mat 2) (z : ℂ) :
    A.charpoly.eval z = quadratic A z := by
  simp [Matrix.charpoly_fin_two, quadratic]

abbrev SpectralCover := {p : RegularMatrix × ℂ // quadratic p.1.val p.2 = 0}
abbrev spectralSpace : TopCat.{0} := TopCat.of SpectralCover

def spectralProjection : spectralSpace ⟶ regularSpace :=
  TopCat.ofHom ⟨fun p => p.val.1, continuous_fst.comp continuous_subtype_val⟩

theorem other_root (A : Mat 2) (z : ℂ) (h : quadratic A z = 0) :
    quadratic A (A.trace - z) = 0 := by
  calc quadratic A (A.trace - z) = quadratic A z := by unfold quadratic; ring
       _ = 0 := h

theorem discriminant_square (s : SpectralCover) :
    discriminant s.val.1.val = (s.val.1.val.trace - 2 * s.val.2) ^ 2 := by
  calc
    discriminant s.val.1.val = (s.val.1.val.trace - 2 * s.val.2) ^ 2 -
        4 * quadratic s.val.1.val s.val.2 := by unfold discriminant quadratic; ring
    _ = (s.val.1.val.trace - 2 * s.val.2) ^ 2 := by rw [s.property]; ring

def deck (s : SpectralCover) : SpectralCover :=
  ⟨(s.val.1, s.val.1.val.trace - s.val.2), other_root _ _ s.property⟩

theorem deck_involution (s : SpectralCover) : deck (deck s) = s := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · rfl
  change s.val.1.val.trace - (s.val.1.val.trace - s.val.2) = s.val.2
  ring

theorem deck_no_fixed (s : SpectralCover) : deck s ≠ s := by
  intro h
  have hz := congrArg (fun p : SpectralCover => p.val.2) h
  have h0 : s.val.1.val.trace - 2 * s.val.2 = 0 := by
    calc s.val.1.val.trace - 2 * s.val.2 =
         (s.val.1.val.trace - s.val.2) - s.val.2 := by ring
         _ = 0 := by rw [show s.val.1.val.trace - s.val.2 = s.val.2 from hz]; ring
  apply s.val.1.property
  rw [discriminant_square s, h0]
  simp

theorem trace_continuous : Continuous fun A : Mat 2 => A.trace := by
  change Continuous (fun A : Mat 2 => ∑ i : Fin 2, A i i)
  exact continuous_finsetSum _ (fun i _ =>
    (continuous_apply i).comp (continuous_apply i))

def deckHomeomorph : SpectralCover ≃ₜ SpectralCover where
  toFun := deck
  invFun := deck
  left_inv := deck_involution
  right_inv := deck_involution
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact
    ((continuous_fst.comp continuous_subtype_val).prodMk
      ((trace_continuous.comp
        (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))).sub
          (continuous_snd.comp continuous_subtype_val)))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact
    ((continuous_fst.comp continuous_subtype_val).prodMk
      ((trace_continuous.comp
        (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))).sub
          (continuous_snd.comp continuous_subtype_val)))

theorem roots_two (A : RegularMatrix) (z w : ℂ)
    (hz : quadratic A.val z = 0) (hw : quadratic A.val w = 0) :
    w = z ∨ w = A.val.trace - z := by
  have hf : (w - z) * (w - (A.val.trace - z)) = 0 := by
    calc (w - z) * (w - (A.val.trace - z)) =
          quadratic A.val w - quadratic A.val z := by unfold quadratic; ring
         _ = 0 := by rw [hw, hz]; ring
  simpa only [sub_eq_zero] using mul_eq_zero.mp hf

abbrev SpectralSteinberg :=
  {p : SpectralCover × SpectralCover // p.1.val.1 = p.2.val.1}

theorem steinberg_two_graphs (p : SpectralSteinberg) :
    p.val.2 = p.val.1 ∨ p.val.2 = deck p.val.1 := by
  have hroot : quadratic p.val.1.val.1.val p.val.2.val.2 = 0 :=
    p.property.symm ▸ p.val.2.property
  rcases roots_two p.val.1.val.1 _ _ p.val.1.property hroot with h | h
  · left; apply Subtype.ext; exact Prod.ext p.property.symm h
  · right; apply Subtype.ext; exact Prod.ext p.property.symm h

theorem spectral_fibre_nonempty (A : RegularMatrix) :
    ∃ z : ℂ, quadratic A.val z = 0 := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root A.val.charpoly (by
    rw [Matrix.charpoly_degree_eq_dim]
    norm_num)
  refine ⟨z, ?_⟩
  change A.val.charpoly.eval z = 0 at hz
  rwa [quadratic_charpoly] at hz

abbrev SteinbergKernel := SpectralSteinberg → ℚ

def diagonalPair (s : SpectralCover) : SpectralSteinberg := ⟨(s, s), rfl⟩
def deckPair (s : SpectralCover) : SpectralSteinberg := ⟨(s, deck s), rfl⟩
def turnFirst (p : SpectralSteinberg) : SpectralSteinberg :=
  ⟨(deck p.val.1, p.val.2), p.property⟩

def convolution (k l : SteinbergKernel) (p : SpectralSteinberg) : ℚ :=
  k (diagonalPair p.val.1) * l p + k (deckPair p.val.1) * l (turnFirst p)

def diagonalKernel : SteinbergKernel := by
  classical
  exact fun p => if p.val.2 = p.val.1 then 1 else 0

def reflectionKernel : SteinbergKernel := by
  classical
  exact fun p => if p.val.2 = deck p.val.1 then 1 else 0

theorem reflection_square : convolution reflectionKernel reflectionKernel = diagonalKernel := by
  classical
  funext p
  rcases p with ⟨⟨x, y⟩, h⟩
  have hc := steinberg_two_graphs ⟨(x, y), h⟩
  change y = x ∨ y = deck x at hc
  rcases hc with hd | ht
  · subst y
    simp [convolution, diagonalKernel, reflectionKernel, diagonalPair, deckPair, turnFirst,
      deck_involution, Ne.symm (deck_no_fixed x)]
  · subst y
    simp [convolution, diagonalKernel, reflectionKernel, diagonalPair, deckPair, turnFirst,
      deck_involution, deck_no_fixed, Ne.symm (deck_no_fixed x)]

def spectralIdempotent (s : SpectralCover) : Mat 2 :=
  (2 * s.val.2 - s.val.1.val.trace)⁻¹ •
    (s.val.1.val - (s.val.1.val.trace - s.val.2) • (1 : Mat 2))

def orthogonalProjector (s : SpectralCover) : Mat 2 :=
  ((spectralIdempotent s * (spectralIdempotent s).conjTranspose).trace)⁻¹ •
    (spectralIdempotent s * (spectralIdempotent s).conjTranspose)

abbrev EigenIncidence :=
  {p : SpectralCover × Flag 2 // p.1.val.1.val * p.2.val 1 = p.1.val.2 • p.2.val 1}
abbrev eigenSpace : TopCat.{0} := TopCat.of EigenIncidence

def eigenProjection : eigenSpace ⟶ spectralSpace :=
  TopCat.ofHom ⟨fun p => p.val.1, continuous_fst.comp continuous_subtype_val⟩

theorem eigenvalue_recovery (p : EigenIncidence) :
    (p.val.1.val.1.val * p.val.2.val 1).trace = p.val.1.val.2 := by
  rw [p.property, Matrix.trace_smul]
  simp [p.val.2.property.trace]

abbrev EigenSteinberg :=
  {p : EigenIncidence × EigenIncidence // p.1.val.1.val.1 = p.2.val.1.val.1}

def eigenSteinbergProjection (p : EigenSteinberg) : SpectralSteinberg :=
  ⟨(p.val.1.val.1, p.val.2.val.1), p.property⟩

structure EigenlineSpectralComparison where
  homeomorphism : EigenIncidence ≃ₜ SpectralCover
  forward : ∀ p : EigenIncidence, homeomorphism p = p.val.1
  inverse_projector : ∀ s : SpectralCover,
    (homeomorphism.symm s).val.2.val 1 = orthogonalProjector s

abbrev spectralLocalSystem : RationalSheaf regularSpace :=
  (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) spectralProjection).obj
    (rationalConstantSheaf spectralSpace)

/-- The direct image along the spectral cover is additive. This restates
`ConstructibleComplexes.pushforward_additive` for this concrete map, where instance
search does not find the generic instance under Lean v4.36. -/
instance spectralPushforwardAdditive :
    (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) spectralProjection).Additive :=
  MathlibExt.AlgebraicGeometry.ConstructibleComplexes.pushforward_additive ℚ _

abbrev spectralDerived : RationalDerived regularSpace :=
  DerivedCategory.Plus.ι.obj
    (((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) spectralProjection).rightDerivedFunctorPlus).obj
      ((DerivedCategory.Plus.singleFunctor (RationalSheaf spectralSpace) 0).obj
        (rationalConstantSheaf spectralSpace)))

def deckMap : spectralSpace ⟶ spectralSpace :=
  TopCat.ofHom ⟨deck, deckHomeomorph.continuous_toFun⟩

theorem deck_over : deckMap ≫ spectralProjection = spectralProjection := by ext p; rfl

def sheafReflection : spectralLocalSystem ⟶ spectralLocalSystem :=
  (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) spectralProjection).map (unitPushforward deckMap) ≫
    eqToHom (by
      change (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (deckMap ≫ spectralProjection)).obj
        (rationalConstantSheaf spectralSpace) = spectralLocalSystem
      rw [deck_over])


def eigenDeck (H : EigenlineSpectralComparison) : EigenIncidence ≃ₜ EigenIncidence :=
  (H.homeomorphism.trans deckHomeomorph).trans H.homeomorphism.symm

theorem eigenDeck_projector (H : EigenlineSpectralComparison) (p : EigenIncidence) :
    (eigenDeck H p).val.2.val 1 = orthogonalProjector (deck p.val.1) := by
  change (H.homeomorphism.symm (deck (H.homeomorphism p))).val.2.val 1 = _
  rw [H.forward, H.inverse_projector]

end MathlibExt.AlgebraicGeometry.RegularGrothendieckSteinberg
