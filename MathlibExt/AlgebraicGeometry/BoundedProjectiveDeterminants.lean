/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ProjectiveDeterminantModules
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Data.Int.Interval

/-!
# Actual alternating determinant of a bounded projective complex

Terms are the native modules of an actual cochain complex. Its support is
the finite set of nonzero terms, not a two-term or constant-amplitude
replacement. The determinant object is the ordered tensor of the actual
exterior-annihilator determinant modules in even degrees and their actual
module duals in odd degrees. It is invertible under the completed generic
projective-determinant proof input.

Knudsen--Mumford quasi-isomorphism/triangle/global descent comparisons are
separate constructors. Computing this object does not claim them from the
two-term determinant source. Arbitrary relative dimension is retained.

References: Knudsen--Mumford, *The projectivity of the moduli space of
stable curvesI*, Sections1-2; Stacks Project, Tags0FJW and0FJX.
The imported module determinant is the exact Axiom-source adapter and
retains its actual exterior maps and original license attribution.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BoundedProjectiveDeterminants

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.Limits
open ProjectiveDeterminantModules
open scoped TensorProduct

variable (R : Type) [CommRing R]

/-- An actual bounded finite-projective cochain complex, in arbitrary degrees. -/
structure Complex where
  cochain : CochainComplex (ModuleCat.{0} R) ℤ
  bounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (cochain.X i)
  [finite : ∀ i, Module.Finite R (cochain.X i)]
  [projective : ∀ i, Module.Projective R (cochain.X i)]

attribute [instance] Complex.finite Complex.projective

variable (C : Complex R)

/-- The actual nonzero term support of this particular complex. -/
def support : Set ℤ := {i | ¬ IsZero (C.cochain.X i)}

theorem support_finite : (support R C).Finite := by
  obtain ⟨a, b, h⟩ := C.bounded
  refine (Set.finite_Icc a b).subset ?_
  intro i hi
  constructor
  · by_contra hx
    exact hi (h i (Or.inl (lt_of_not_ge hx)))
  · by_contra hx
    exact hi (h i (Or.inr (lt_of_not_ge hx)))

/-- Order the actual finite support by cochain degree. -/
def degrees : List ℤ := (support_finite R C).toFinset.sort (· ≤ ·)

/-- Actual determinant in even degrees and actual dual determinant in odd degrees. -/
def term (i : ℤ) : ModuleCat.{0} R := by
  classical
  exact if Even i then ModuleCat.of R (determinantModule R (C.cochain.X i))
    else ModuleCat.of R (Module.Dual R (determinantModule R (C.cochain.X i)))

/-- The literal ordered tensor of a given finite degree list. -/
def tensorTerms (is : List ℤ) : ModuleCat.{0} R :=
  is.foldr (fun i M ↦ term R C i ⊗ M) (𝟙_ (ModuleCat.{0} R))

/-- The alternating determinant module of the actual bounded complex. -/
def determinantObject : ModuleCat.{0} R := tensorTerms R C (degrees R C)

/-- An actual cochain isomorphism preserves the nonzero term support. -/
theorem support_eq_of_iso (D : Complex R) (e : C.cochain ≅ D.cochain) :
    support R C = support R D := by
  ext i
  exact not_congr ((HomologicalComplex.eval _ _ i).mapIso e).isZero_iff

/-- The ordered degree list is independent of an isomorphic presentation. -/
theorem degrees_eq_of_iso (D : Complex R) (e : C.cochain ≅ D.cochain) :
    degrees R C = degrees R D := by
  classical
  simp only [degrees]
  congr 1
  ext i
  simp only [Set.Finite.mem_toFinset, support_eq_of_iso R C D e]

/-- The determinant transport of one term is its literal exterior map,
or the inverse dual map in odd degree. -/
def termIso (D : Complex R) (e : C.cochain ≅ D.cochain) (i : ℤ) :
    term R C i ≅ term R D i := by
  classical
  let component : C.cochain.X i ≅ D.cochain.X i :=
    (HomologicalComplex.eval _ _ i).mapIso e
  let a : determinantModule R (C.cochain.X i) ≃ₗ[R]
      determinantModule R (D.cochain.X i) :=
    determinantEquiv component.toLinearEquiv
  by_cases h : Even i
  · simpa only [term, h, ite_true] using a.toModuleIso
  · simpa only [term, h, ite_false] using a.symm.dualMap.toModuleIso

/-- Transport on an ordered tensor uses the native tensor isomorphisms. -/
def tensorTermsIso (D : Complex R) (e : C.cochain ≅ D.cochain) :
    (is : List ℤ) → tensorTerms R C is ≅ tensorTerms R D is
  | [] => Iso.refl _
  | i :: is => tensorIso (termIso R C D e i) (tensorTermsIso D e is)

/-- The determinant of an actual cochain isomorphism, with no arbitrary
line comparison or scalar rescaling. -/
def determinantIso (D : Complex R) (e : C.cochain ≅ D.cochain) :
    determinantObject R C ≅ determinantObject R D :=
  tensorTermsIso R C D e (degrees R C) ≪≫
    eqToIso (congrArg (tensorTerms R D) (degrees_eq_of_iso R C D e))

/-- Determinant modules of finite projective modules are invertible: an instance of this class
asserts that, for every finite projective $R$-module $M$, the determinant module of $M$
(`determinantModule`, the submodule of the exterior algebra of $M$ annihilated by left
multiplication by every element of $M$) is an invertible $R$-module. -/
class ProjectiveSources : Prop where
  invertible : ∀ M : ModuleCat.{0} R, Module.Finite R M → Module.Projective R M →
    Module.Invertible R (determinantModule R M)

variable [D : ProjectiveSources R]

theorem term_invertible (i : ℤ) : Module.Invertible R (term R C i) := by
  classical
  have : Module.Invertible R (determinantModule R (C.cochain.X i)) :=
    D.invertible (C.cochain.X i) inferInstance inferInstance
  by_cases h : Even i
  · have ht : term R C i = ModuleCat.of R (determinantModule R (C.cochain.X i)) := by
      simp [term, h]
    rw [ht]
    exact this
  · have ht : term R C i =
        ModuleCat.of R (Module.Dual R (determinantModule R (C.cochain.X i))) := by
      simp [term, h]
    rw [ht]
    infer_instance

theorem tensorTerms_invertible (is : List ℤ) : Module.Invertible R (tensorTerms R C is) := by
  induction is with
  | nil => exact inferInstanceAs (Module.Invertible R R)
  | cons i is ih =>
    have := term_invertible R C i
    have := ih
    exact inferInstanceAs (Module.Invertible R (term R C i ⊗[R] tensorTerms R C is))

theorem determinantObject_invertible : Module.Invertible R (determinantObject R C) :=
  tensorTerms_invertible R C _

end MathlibExt.AlgebraicGeometry.BoundedProjectiveDeterminants
