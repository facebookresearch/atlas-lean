/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import MathlibExt.AlgebraicGeometry.ConstructibleComplexes

@[expose] public noncomputable section

/-!
# The exponential cover for algebraic nearby cycles

A regular function is an actual global scheme section. Its value on
complex points defines the punctured domain, the zero subspace and the
pullback of exp(2πiz). The integral deck transformation is translation of
the second coordinate. A reduced zero-fiber presentation is pinned to the
actual zero subspace by a homeomorphism commuting with its inclusion.
No sheaf functors or monodromy operators are supplied as geometric data.

Sources: A. Dimca, *Sheaves in Topology*, §4.2;
de Cataldo--Migliorini, *The decomposition theorem, perverse sheaves and
the topology of algebraic maps*, nearby and vanishing cycles.
-/

namespace MathlibExt.AlgebraicGeometry.NearbyCycleGeometry

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.ComplexAnalytification
open _root_.MathlibExt.AlgebraicGeometry.PerverseSheaves

/-- Evaluation of the actual global regular function. -/
def regularValue (X : ComplexScheme) (s : Γ(X.left, ⊤)) (p : space X) : ℂ :=
  ComplexPoints.eval s p (by simp [ComplexPoints.Mem])

set_option backward.isDefEq.respectTransparency false in
lemma regularValue_continuous (X : ComplexScheme) (s : Γ(X.left, ⊤)) :
    Continuous (regularValue X s) := by
  rw [continuous_def]
  intro V hV
  have e : regularValue X s ⁻¹' V =
      ComplexPoints.basicSet (y := X.hom) ⊤ s V := by
    ext p
    constructor
    · intro hp
      exact ⟨by simp [ComplexPoints.Mem], hp⟩
    · rintro ⟨hp, h⟩
      exact h
  rw [e]
  exact ComplexPoints.isOpen_basicSet ⊤ s hV

/-- The actual punctured domain of the regular function. -/
def punctured (X : ComplexScheme) (s : Γ(X.left, ⊤)) : TopCat.{0} :=
  TopCat.of {p : space X // regularValue X s p ≠ 0}

/-- Inclusion of that punctured domain. -/
def puncturedInclusion (X : ComplexScheme) (s : Γ(X.left, ⊤)) :
    punctured X s ⟶ space X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The closed zero subspace, with its actual subspace topology. -/
def zeroSpace (X : ComplexScheme) (s : Γ(X.left, ⊤)) : TopCat.{0} :=
  TopCat.of {p : space X // regularValue X s p = 0}

/-- A reduced algebraic presentation of the actual zero subspace. -/
structure ZeroFiber (X : ComplexScheme) (s : Γ(X.left, ⊤)) where
  Z : ComplexScheme
  [variety : IsComplexVariety Z]
  i : Z ⟶ X
  [closed : IsClosedImmersion i.left]
  comparison : space Z ≃ₜ zeroSpace X s
  inclusion_eq : ∀ p : space Z, (comparison p).val = spaceMap i p

attribute [instance] ZeroFiber.variety ZeroFiber.closed

/-- The pulled-back universal cover, using exp(2πiz). -/
def exponentialCover (X : ComplexScheme) (s : Γ(X.left, ⊤)) : TopCat.{0} :=
  TopCat.of {p : space X × ℂ //
    regularValue X s p.1 = Complex.exp (2 * Real.pi * Complex.I * p.2)}

/-- Projection of the actual cover to the source variety. -/
def coverProjection (X : ComplexScheme) (s : Γ(X.left, ⊤)) :
    exponentialCover X s ⟶ space X :=
  TopCat.ofHom ⟨fun p ↦ p.val.1, continuous_fst.comp continuous_subtype_val⟩

/-- Projection to the punctured domain. -/
def puncturedProjection (X : ComplexScheme) (s : Γ(X.left, ⊤)) :
    exponentialCover X s ⟶ punctured X s :=
  TopCat.ofHom ⟨fun p ↦ ⟨p.val.1, by rw [p.property]; exact Complex.exp_ne_zero _⟩,
    (continuous_fst.comp continuous_subtype_val).subtype_mk _⟩

@[simp] lemma puncturedProjection_comp (X : ComplexScheme) (s : Γ(X.left, ⊤)) :
    puncturedProjection X s ≫ puncturedInclusion X s = coverProjection X s := rfl

/-- The actual integral deck translation of the exponential cover. -/
def deck (X : ComplexScheme) (s : Γ(X.left, ⊤)) (n : ℤ) :
    exponentialCover X s ≃ₜ exponentialCover X s where
  toFun p := ⟨(p.val.1, p.val.2 + n), by
    rw [p.property]
    rw [mul_add, Complex.exp_add]
    have e : Complex.exp (2 * Real.pi * Complex.I * (n : ℂ)) = 1 := by
      rw [mul_comm (2 * Real.pi * Complex.I) (n : ℂ)]
      exact Complex.exp_int_mul_two_pi_mul_I n
    rw [e, mul_one]⟩
  invFun p := ⟨(p.val.1, p.val.2 - n), by
    rw [p.property]
    rw [mul_sub, Complex.exp_sub]
    have e : Complex.exp (2 * Real.pi * Complex.I * (n : ℂ)) = 1 := by
      rw [mul_comm (2 * Real.pi * Complex.I) (n : ℂ)]
      exact Complex.exp_int_mul_two_pi_mul_I n
    rw [e, div_one]⟩
  left_inv p := by apply Subtype.ext; simp
  right_inv p := by apply Subtype.ext; simp
  continuous_toFun := ((continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).add continuous_const)).subtype_mk _
  continuous_invFun := ((continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).sub continuous_const)).subtype_mk _

/-- The deck automorphism in the actual topological category. -/
def deckIso (X : ComplexScheme) (s : Γ(X.left, ⊤)) (n : ℤ) :
    exponentialCover X s ≅ exponentialCover X s :=
  TopCat.isoOfHomeo (deck X s n)

@[simp] lemma deckProjection (X : ComplexScheme) (s : Γ(X.left, ⊤)) (n : ℤ) :
    (deckIso X s n).hom ≫ coverProjection X s = coverProjection X s := rfl

@[simp] lemma deck_add_apply (X : ComplexScheme) (s : Γ(X.left, ⊤))
    (m n : ℤ) (p : exponentialCover X s) :
    deck X s (m + n) p = deck X s n (deck X s m p) := by
  apply Subtype.ext
  change (p.val.1, p.val.2 + ((m + n : ℤ) : ℂ)) =
    (p.val.1, (p.val.2 + (m : ℂ)) + (n : ℂ))
  simp [add_assoc]

/-- Morphisms over the regular function, including the actual pulled-back
regular-section equality and zero-fiber square. -/
structure FunctionMorphism {X Y : ComplexScheme} {s : Γ(X.left, ⊤)} {t : Γ(Y.left, ⊤)}
    (A : ZeroFiber X s) (B : ZeroFiber Y t) where
  g : X ⟶ Y
  function_eq : g.left.app ⊤ t = s
  g₀ : A.Z ⟶ B.Z
  zero_square : A.i ≫ g = g₀ ≫ B.i

set_option backward.isDefEq.respectTransparency false in
lemma regularValue_map {X Y : ComplexScheme} {s : Γ(X.left, ⊤)} {t : Γ(Y.left, ⊤)}
    {A : ZeroFiber X s} {B : ZeroFiber Y t} (G : FunctionMorphism A B) (p : space X) :
    regularValue Y t (spaceMap G.g p) = regularValue X s p := by
  change ComplexPoints.eval t (ComplexPoints.map G.g.left G.g.w p) _ =
    ComplexPoints.eval s p _
  rw [ComplexPoints.eval_map_point G.g.left G.g.w t p]
  rw [G.function_eq]

/-- The actual map between exponential pullback covers. -/
def coverMap {X Y : ComplexScheme} {s : Γ(X.left, ⊤)} {t : Γ(Y.left, ⊤)}
    {A : ZeroFiber X s} {B : ZeroFiber Y t} (G : FunctionMorphism A B) :
    exponentialCover X s ⟶ exponentialCover Y t :=
  TopCat.ofHom ⟨fun p ↦ ⟨(spaceMap G.g p.val.1, p.val.2), by
    rw [regularValue_map G p.val.1]; exact p.property⟩,
    (((spaceMap G.g).hom.continuous.comp
      (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _⟩

@[simp] lemma coverMap_square {X Y : ComplexScheme}
    {s : Γ(X.left, ⊤)} {t : Γ(Y.left, ⊤)}
    {A : ZeroFiber X s} {B : ZeroFiber Y t} (G : FunctionMorphism A B) :
    coverMap G ≫ coverProjection Y t = coverProjection X s ≫ spaceMap G.g := rfl

end MathlibExt.AlgebraicGeometry.NearbyCycleGeometry

