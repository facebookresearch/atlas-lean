/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AlgebraicEquivariantChowModels
public import MathlibExt.AlgebraicGeometry.StackVirtualPullbacks

/-!
# Actual character sections and equivariant first Chern operations

For a character chi, sections over an affine quotient-stack point are
regular functions on its actual torsor satisfying f(gp)=chi(g) f(p).
The scalar action comes from the original torsor projection. The stack
line is fixed by these sections and all original affine-point arrows.
Its Euler operation is the native zero-section push/homotopy inverse.

Reference: Graber--Pandharipande alg-geom/9708001v2, Section1;
Edidin--Graham equivariant Chow and Kresch quotient-stack convention.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.EquivariantCharacterLineModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open GroupTorsorGeometry AlgebraicWeightBundleModels AlgebraicEquivariantChowModels
open StackCycleGeometry StackAffineModules StackVectorBundles StackChowGroups StackBundleCones
open StackCycleRelations StackFibreModels
open scoped TensorProduct

variable {T : Over base} (chi : Character Gm) (P : Torsor Gm T)

def IsCharacterSection (s : Γ(P.total.left, ⊤)) : Prop :=
  P.action.smul.left.appTop.hom s = characterFunction chi P.total * (snd Gm P.total).left.appTop.hom
    s

/-- The section module uses exactly the actual torsor-projection scalar map. -/
def characterSections (chi : Character Gm) (P : Torsor Gm T) :
    letI := P.projection.left.appTop.hom.toAlgebra
    Submodule Γ(T.left, ⊤) Γ(P.total.left, ⊤) := by
  letI := P.projection.left.appTop.hom.toAlgebra
  refine ({
    carrier := {s | IsCharacterSection chi P s}
    zero_mem' := by
      change IsCharacterSection chi P 0
      simp only [IsCharacterSection, map_zero, mul_zero]
    add_mem' := by
      intro s t hs ht
      change IsCharacterSection chi P (s+t)
      change IsCharacterSection chi P s at hs
      change IsCharacterSection chi P t at ht
      simp only [IsCharacterSection, map_add, mul_add] at *
      rw [hs, ht]
    smul_mem' := ?_ } : Submodule Γ(T.left, ⊤) Γ(P.total.left, ⊤))
  intro r s hs
  change P.action.smul.left.appTop.hom (P.projection.left.appTop.hom r * s) =
    characterFunction chi P.total * (snd Gm P.total).left.appTop.hom (P.projection.left.appTop.hom r
      * s)
  have h := congrArg (fun a : Gm ⊗ P.total ⟶ T => a.left.appTop.hom r) P.invariant
  simp only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at h
  change P.action.smul.left.appTop.hom (P.projection.left.appTop.hom r) =
    (snd Gm P.total).left.appTop.hom (P.projection.left.appTop.hom r) at h
  change IsCharacterSection chi P s at hs
  unfold IsCharacterSection at hs
  rw [map_mul, map_mul, h, hs]
  ring

variable {X : Over base} [ModObj Gm X] (Q : EquivariantSource X)

/-- A quotient-point arrow supplies the literal map of the original total torsors. -/
def torsorMap {a b : AffinePoint Q.quotient.stack} (f : a ⟶ b) :=
  (((Q.quotient.fibre a.obj.base).functor.map f.hom.fiber).iso.hom) ≫
    (Q.quotient.restriction f.hom.base b.obj.fiber).iso.hom ≫
      (Q.quotient.reindex f.hom.base b.obj.fiber).original Gm

/-- No line presheaf is independent of the actual equivariant regular functions. -/
structure CharacterModule (chi : Character Gm) where
  module : FPModule Q.quotient.stack
  rank : HasConstantRank module 1
  identification : ∀ a : (AffinePoint Q.quotient.stack)ᵒᵖ,
    let T := a.unop.obj.base
    let P := ((Q.quotient.fibre T).functor.obj a.unop.obj.fiber).torsor
    letI := P.projection.left.appTop.hom.toAlgebra
    module.presheaf.obj a ≃ₗ[Γ(T.left, ⊤)] characterSections chi P
  arrows : ∀ {a b : (AffinePoint Q.quotient.stack)ᵒᵖ} (f : a ⟶ b)
    (s : module.presheaf.obj a),
    ((identification b (module.presheaf.restrictₛₗ f s)).val) =
      (torsorMap Q f.unop).left.appTop ((identification a s).val)

/-- The represented line is the section total stack of that same module. -/
structure CharacterLine (chi : Character Gm) where
  sections : CharacterModule Q chi
  bundle : VectorBundle Q.quotient.stack
  rank : bundle.rank = 1
  module_eq : bundle.module.val = sections.module

variable (D : CycleConstructionData base (FiniteTypeArtin ℂ)) (K : KreschPresentation D)

/-- Chern data contains only native geometric maps and their homotopy/descent proofs. -/
structure CharacterChernData (chi : Character Gm) where
  line : CharacterLine Q chi
  inScope : FiniteTypeArtin ℂ line.bundle.total
  projection : FlatChowPullData D K inScope Q.inScope line.bundle.projection line.bundle.rank
  homotopy : BundleHomotopyData D K Q.inScope line.bundle inScope projection
  zero : ZeroSection line.bundle
  push : ProjectiveChowPushData D K Q.inScope inScope zero.map

/-- The character first Chern cap is the already defined zero-section recipe. -/
def characterFirstChern {chi : Character Gm} (C : CharacterChernData Q D K chi) (i : ℤ) :
    EquivariantChow D K Q i →ₗ[ℚ] EquivariantChow D K Q (i-1) :=
  (rationalMap (chowRegrade D K Q.quotient.stack Q.inScope (by omega))).comp
    (rationalMap (firstChernOperator C.homotopy C.zero C.push C.line.rank (i-1)))

end MathlibExt.AlgebraicGeometry.EquivariantCharacterLineModels
