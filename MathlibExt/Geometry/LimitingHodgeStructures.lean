/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import MathlibExt.Geometry.RationalHodgeStructures
public import MathlibExt.AlgebraicGeometry.ConstructibleComplexes

/-!
# Polarized period data and limiting mixed Hodge realizations

The rational sheaf is the sheafification of the actual presheaf of equivariant
locally constant functions on the exponential cover. Period filtrations are
holomorphic subbundles in fixed complex coordinates and satisfy the actual
Griffiths derivative condition. The logarithm and exponential are explicit
finite endomorphism polynomials. The limiting filtration is fixed by a
holomorphic extension of the untwisted period filtration at zero.

Convention: equivariant sections satisfy `s(z+1)=T s(z)`; positive-loop
parallel transport is therefore `T⁻¹`. The period deck operator is `T`, as
in the displayed untwisting formula. Its logarithm differs by a sign from
the parallel-transport logarithm, leaving the monodromy weight filtration
unchanged.

Sources: Schmid, *Variation of Hodge Structure: The Singularities of the
Period Mapping*, Invent. Math. 22 (1973), §§4 and 6; Peters--Steenbrink,
*Mixed Hodge Structures*, Chapter 11.
-/

@[expose] public noncomputable section

namespace MathlibExt.Geometry.LimitingHodgeStructures

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RationalHodgeStructures

/-- The actual upper half plane. -/
def upperHalfPlane : TopCat.{0} := TopCat.of {z : ℂ | 0 < z.im}

/-- The punctured unit disk. -/
def puncturedDisk : TopCat.{0} := TopCat.of {t : ℂ | t ≠ 0 ∧ ‖t‖ < 1}

/-- The normalized exponential covering map. -/
def exponentialCover : upperHalfPlane ⟶ puncturedDisk :=
  TopCat.ofHom
    ⟨fun z ↦ ⟨Complex.exp (2 * Real.pi * Complex.I * z.1), by
      constructor
      · exact Complex.exp_ne_zero _
      · rw [Complex.norm_exp]
        have h : (2 * Real.pi * Complex.I * z.1).re = -2 * Real.pi * z.1.im := by
          simp [Complex.mul_re, Complex.mul_im]
        rw [h, Real.exp_lt_one_iff]
        have hz : 0 < z.1.im := z.2
        have hp := Real.pi_pos
        nlinarith⟩, by fun_prop⟩

/-- The positive translation on the cover. -/
def deck (z : upperHalfPlane) : upperHalfPlane :=
  ⟨z.1 + 1, by simpa using z.2⟩

theorem exponentialCover_deck (z : upperHalfPlane) :
    exponentialCover (deck z) = exponentialCover z := by
  apply Subtype.ext
  change Complex.exp (2 * Real.pi * Complex.I * (z.1 + 1)) =
    Complex.exp (2 * Real.pi * Complex.I * z.1)
  rw [mul_add, mul_one, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The inverse image of an actual disk open under the fixed cover. -/
abbrev coveredOpen (U : Opens puncturedDisk) :=
  {z : upperHalfPlane | exponentialCover z ∈ U}

/-- Deck action on the inverse image of an open. -/
def deckOnOpen (U : Opens puncturedDisk) (z : coveredOpen U) : coveredOpen U :=
  ⟨deck z.1, by
    change exponentialCover (deck z.1) ∈ U
    rw [exponentialCover_deck]
    exact z.2⟩

/-- Equivariant locally constant sections; the actual deck condition is
imposed on actual functions, rather than on an unrelated sheaf. -/
def equivariantSections (V : ModuleCat.{0} ℚ) (T : V ≃ₗ[ℚ] V)
    (U : Opens puncturedDisk) : Submodule ℚ (LocallyConstant (coveredOpen U) V) where
  carrier := {s | ∀ z, s (deckOnOpen U z) = T (s z)}
  zero_mem' := by intro z; simp
  add_mem' := by intro s t hs ht z; simp only [LocallyConstant.add_apply, hs z, ht z, map_add]
  smul_mem' := by
    intro c s hs z
    simp only [LocallyConstant.smul_apply, hs z, map_smul]

/-- Restriction of sections to a smaller disk open. -/
def restrictCover {U V : Opens puncturedDisk} (h : V ≤ U) :
    C(coveredOpen V, coveredOpen U) :=
  ⟨fun z ↦ ⟨z.1, h z.2⟩, by fun_prop⟩

/-- The presheaf defining the rational local system of the period deck
operator. Its value and all its restrictions are fixed explicitly. -/
def equivariantPresheaf (V : ModuleCat.{0} ℚ) (T : V ≃ₗ[ℚ] V) :
    (Opens puncturedDisk)ᵒᵖ ⥤ ModuleCat.{0} ℚ where
  obj U := ModuleCat.of ℚ (equivariantSections V T U.unop)
  map {U W} h := ModuleCat.ofHom
    { toFun := fun s ↦ ⟨LocallyConstant.comap (restrictCover h.unop.le) s.1, by
        intro z
        exact s.2 ⟨z.1, h.unop.le z.2⟩⟩
      map_add' := by intro s t; rfl
      map_smul' := by intro c s; rfl }
  map_id U := by ext s z; rfl
  map_comp f g := by ext s z; rfl

/-- The actual rational sheaf of equivariant locally constant sections. -/
def rationalLocalSystem (V : ModuleCat.{0} ℚ) (T : V ≃ₗ[ℚ] V) :
    TopCat.Sheaf (ModuleCat.{0} ℚ) puncturedDisk :=
  (presheafToSheaf (Opens.grothendieckTopology puncturedDisk)
    (ModuleCat.{0} ℚ)).obj (equivariantPresheaf V T)

variable {V : ModuleCat.{0} ℚ} (C : RationalComplexification V)
  {r : ℕ} (e : C.complexSpace ≃ₗ[ℂ] EuclideanSpace ℂ (Fin r))

/-- A filtration is a holomorphic subbundle if it has local holomorphic
frames of exactly its fixed fiber subspaces. -/
def HolomorphicFiltrationOn (F : ℂ → ℤ → Submodule ℂ C.complexSpace) (U : Set ℂ) : Prop :=
  ∀ z ∈ U, ∀ p : ℤ, ∃ ε : ℝ, 0 < ε ∧ Metric.ball z ε ⊆ U ∧
    ∃ n : ℕ, ∃ s : Fin n → ℂ → EuclideanSpace ℂ (Fin r),
      (∀ i, DifferentiableOn ℂ (s i) (Metric.ball z ε)) ∧
      ∀ u ∈ Metric.ball z ε,
        LinearIndependent ℂ (fun i ↦ s i u) ∧
        (F u p).map e.toLinearMap = Submodule.span ℂ (Set.range fun i ↦ s i u)

/-- Griffiths transversality for every actual local holomorphic section. -/
def GriffithsTransverse (F : ℂ → ℤ → Submodule ℂ C.complexSpace) : Prop :=
  ∀ (z : ℂ) (_ : 0 < z.im) (p : ℤ) (ε : ℝ), 0 < ε →
    Metric.ball z ε ⊆ {u : ℂ | 0 < u.im} →
    ∀ s : ℂ → EuclideanSpace ℂ (Fin r),
      DifferentiableOn ℂ s (Metric.ball z ε) →
      (∀ u ∈ Metric.ball z ε, e.symm (s u) ∈ F u p) →
      e.symm (deriv s z) ∈ F z (p - 1)

/-- A rational polarization with the actual complexified bilinear form and
the Hodge--Riemann sign on the exact `(p,q)` subspaces. -/
structure RationalPolarization (w : ℤ)
    (F : ℂ → ℤ → Submodule ℂ C.complexSpace) where
  rationalForm : V →ₗ[ℚ] V →ₗ[ℚ] ℚ
  complexForm : C.complexSpace →ₗ[ℂ] C.complexSpace →ₗ[ℂ] ℂ
  comparison : ∀ x y,
    complexForm (C.comparisonMap x) (C.comparisonMap y) =
      algebraMap ℚ ℂ (rationalForm x y)
  parity : ∀ x y, complexForm x y = (-1 : ℂ) ^ w * complexForm y x
  nondegenerate : ∀ x, (∀ y, complexForm x y = 0) → x = 0
  orthogonal : ∀ z, 0 < z.im → ∀ p x y,
    x ∈ F z p → y ∈ F z (w + 1 - p) → complexForm x y = 0
  positive : ∀ z, 0 < z.im → ∀ p q : ℤ, p + q = w → ∀ x,
    x ≠ 0 → x ∈ F z p → x ∈ (F z q).map C.conjugation.toLinearMap →
      0 < (Complex.I ^ (p - q) * (-1 : ℂ) ^ (w * (w - 1) / 2) *
        complexForm x (C.conjugation x)).re

/-- A polarized one-variable period variation. Its rational local system
is fixed by `rationalLocalSystem` of its actual rational deck operator. -/
structure PolarizedPeriodVariation (w : ℤ) where
  rationalDeck : V ≃ₗ[ℚ] V
  complexDeck : C.complexSpace ≃ₗ[ℂ] C.complexSpace
  deck_comparison : ∀ v,
    complexDeck (C.comparisonMap v) = C.comparisonMap (rationalDeck v)
  F : ℂ → ℤ → Submodule ℂ C.complexSpace
  pure : ∀ z, 0 < z.im → ∃ H : PureHodgeStructure C w, H.F = F z
  holomorphic : HolomorphicFiltrationOn C e F {z : ℂ | 0 < z.im}
  transverse : GriffithsTransverse C e F
  polarization : RationalPolarization C w F
  polarized_deck : ∀ x y,
    polarization.rationalForm (rationalDeck x) (rationalDeck y) =
      polarization.rationalForm x y
  deck_filtration : ∀ z, 0 < z.im → ∀ p,
    F (z + 1) p = (F z p).map complexDeck.toLinearMap

/-- Finite polynomial logarithm of a specified unipotent rational deck
operator, with an explicit nilpotency bound. -/
def rationalLog {w : ℤ} (H : PolarizedPeriodVariation C e w) (b : ℕ) : Module.End ℚ V :=
  ∑ i ∈ Finset.range b, if i = 0 then 0 else
    ((-1 : ℚ) ^ (i + 1) / i) • (H.rationalDeck.toLinearMap - 1) ^ i

/-- The same finite logarithm on the actual complexification. -/
def complexLog {w : ℤ} (H : PolarizedPeriodVariation C e w) (b : ℕ) :
    Module.End ℂ C.complexSpace :=
  ∑ i ∈ Finset.range b, if i = 0 then 0 else
    ((-1 : ℂ) ^ (i + 1) / i) • (H.complexDeck.toLinearMap - 1) ^ i

/-- The finite exponential of the nilpotent logarithm. -/
def nilpotentExp (N : Module.End ℂ C.complexSpace) (b : ℕ) (z : ℂ) :
    Module.End ℂ C.complexSpace :=
  ∑ i ∈ Finset.range b, (z ^ i / (i.factorial : ℂ)) • N ^ i

/-- The monodromy filtration centered at `w`, written directly in terms of
the actual kernels and images of powers of the logarithm. With `N^b=0`,
this is `Σ_j ker(N^(k-w+j+1)) ∩ im(N^j)`; negative exponents give `ker(1)=0`. -/
def monodromyWeight (N : Module.End ℚ V) (b : ℕ) (w k : ℤ) : Submodule ℚ V :=
  ⨆ j : Fin b, LinearMap.ker (N ^ (k - w + (j : ℤ) + 1).toNat) ⊓
    LinearMap.range (N ^ (j : ℕ))

/-- An extension of the actual untwisted filtration to the whole unit disk.
Its value at zero, rather than an arbitrarily chosen flag, is the limit. -/
structure PeriodExtension {w : ℤ} (H : PolarizedPeriodVariation C e w) (b : ℕ) where
  F : ℂ → ℤ → Submodule ℂ C.complexSpace
  holomorphic : HolomorphicFiltrationOn C e F {t : ℂ | ‖t‖ < 1}
  limit_filtration : Antitone (F 0)
  normalized : ∀ z, 0 < z.im → ∀ p,
    F (Complex.exp (2 * Real.pi * Complex.I * z)) p =
      (H.F z p).map (nilpotentExp C (complexLog C e H b) b (-z))

/-- A limiting MHS on the fixed rational carrier, with the exact limit F
and the exact kernel/image monodromy W. -/
structure LimitingHodgeData {w : ℤ} (H : PolarizedPeriodVariation C e w) (b : ℕ)
    (E : PeriodExtension C e H b) where
  mixed : MixedHodgeStructure C
  weight : ∀ k, mixed.W k = monodromyWeight (rationalLog C e H b) b w k
  hodge : mixed.F = E.F 0
  logarithm_lowers_hodge : ∀ p,
    (mixed.F p).map (complexLog C e H b) ≤ mixed.F (p - 1)

end MathlibExt.Geometry.LimitingHodgeStructures
