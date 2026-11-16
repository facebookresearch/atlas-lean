/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HallConvolutionOperations

/-!
# The actual semiclassical multiplication and divided commutator

BG_m is the native stack of line bundles, identified on every scheme
test and coherently with module pullback. Its geometric product action
is the inverse of L−1 in K(St/C); the proof of that source identity is
requested separately. The divided commutator is computed by applying
this particular BG_m product to the actual Hall commutator.

Regular closure and descent through (L−1) are proofs about those fixed
operations. Neither a scalar inverse nor an arbitrary bracket is an
input. Algebra, commutativity and Poisson laws remain separate requests.

References: Bridgeland, arXiv:1002.4372v1, §3.3 (the GL_n inverses);
arXiv:1002.4374v3, §5.1 and Theorem 5.1.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HallSemiclassicalOperations

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open StackCycleGeometry
open GeometricHallStackFunctions HallFamilyStackModels HallConvolutionOperations
open CoherentCurveLinearSeries AlgebraicBundleGeometry

/-- The genuine groupoid of line bundles and module isomorphisms. -/
abbrev LineFamily (T : Over (Spec (.of ℂ))) :=
  {L : T.left.Modules // IsLine L}

instance lineFamilyCategory (T : Over (Spec (.of ℂ))) : Category (LineFamily T) where
  Hom L K := L.val ≅ K.val
  id _ := Iso.refl _
  comp a b := a ≪≫ b
  id_comp _ := by apply Iso.ext; exact Category.id_comp _
  comp_id _ := by apply Iso.ext; exact Category.comp_id _
  assoc _ _ _ := by apply Iso.ext; exact Category.assoc _ _ _

instance lineFamilyIsGroupoid (T : Over (Spec (.of ℂ))) : IsGroupoid (LineFamily T) where
  all_isIso a :=
    ⟨⟨a.symm,by apply Iso.ext; exact a.hom_inv_id,
      by apply Iso.ext; exact a.inv_hom_id⟩⟩

def lineModules (T : Over (Spec (.of ℂ))) : LineFamily T ⥤ T.left.Modules where
  obj L := L.val
  map a := a.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A full fibre description of BG_m by actual line-bundle families. -/
structure ClassifyingLineStackData where
  carrier : FiniteTypeStack
  fibre : ∀ T : Over (Spec (.of ℂ)), carrier.stack.Fibre T ≌ LineFamily T

namespace ClassifyingLineStackData

def moduleForget (B : ClassifyingLineStackData) (T : Over (Spec (.of ℂ))) :=
  (B.fibre T).functor ⋙ lineModules T

end ClassifyingLineStackData

/-- The line stack is normalized on objects, arrows and native pullback coherence. -/
structure ClassifyingLineStackModel extends ClassifyingLineStackData where
  moduleComparison : ∀ {T U : Over (Spec (.of ℂ))} (f : U ⟶ T),
    pull carrier.stack f ⋙ toClassifyingLineStackData.moduleForget U ≅
      toClassifyingLineStackData.moduleForget T ⋙ Scheme.Modules.pullback f.left
  unit : ∀ (T : Over (Spec (.of ℂ))) (L : carrier.stack.Fibre T),
    (moduleComparison (𝟙 T)).hom.app L ≫
      (Scheme.Modules.pullbackId T.left).hom.app
        ((toClassifyingLineStackData.moduleForget T).obj L) =
    (toClassifyingLineStackData.moduleForget T).map
      ((Cat.Hom.toNatIso (carrier.stack.toPseudofunctor.mapId (.mk (op T)))).hom.app L)
  composition : ∀ {T U V : Over (Spec (.of ℂ))} (f : U ⟶ T) (g : V ⟶ U)
    (L : carrier.stack.Fibre T),
    (moduleComparison (g ≫ f)).hom.app L =
    (toClassifyingLineStackData.moduleForget V).map
      ((Cat.Hom.toNatIso
        (carrier.stack.toPseudofunctor.mapComp f.op.toLoc g.op.toLoc)).hom.app L) ≫
      (moduleComparison g).hom.app ((pull carrier.stack f).obj L) ≫
      (Scheme.Modules.pullback g.left).map ((moduleComparison f).hom.app L) ≫
      (Scheme.Modules.pullbackComp g.left f.left).hom.app
        ((toClassifyingLineStackData.moduleForget T).obj L)

variable {X : Over (Spec (.of ℂ))} {H : HallStacks X} {D : ConvolutionModels H}
  {h : ConvolutionDescent D} {L : ∀ g : Generator H.moduli, LefschetzProduct g}
  {hL : LefschetzDescent L}

/-- A genuine BG_m product, with regularity of the computed divided commutators. -/
structure DividedCommutatorData (C : RegularClosure h hL) where
  lines : ClassifyingLineStackModel
  product : ScalarProductModels H.moduli lines.carrier
  descent : ScalarDescent product
  regular : ∀ a b : Regular H.moduli,
    scalarAction descent (convolution h a.val b.val - convolution h b.val a.val) ∈
      regularSubmodule H.moduli

/-- Division by L−1 is this BG_m product of the actual Hall commutator. -/
def dividedCommutator {C : RegularClosure h hL} (B : DividedCommutatorData C) :
    Regular H.moduli →ₗ[ℂ] Regular H.moduli →ₗ[ℂ] Regular H.moduli :=
  LinearMap.mk₂ ℂ (fun a b =>
      ⟨scalarAction B.descent (convolution h a.val b.val - convolution h b.val a.val),
        B.regular a b⟩)
    (by intros; apply Subtype.ext; simp [add_sub_add_comm])
    (by intros; apply Subtype.ext; simp [smul_sub])
    (by intros; apply Subtype.ext; simp [add_sub_add_comm])
    (by intros; apply Subtype.ext; simp [smul_sub])

/-- The quotient's product before its two arguments are descended. -/
def rawSemiclassicalMultiplication (C : RegularClosure h hL) :
    Regular H.moduli →ₗ[ℂ] Regular H.moduli →ₗ[ℂ] Semiclassical C :=
  (regularMultiplication C).compr₂ (semiclassicalRelations C).mkQ

/-- The ideal property concerns the already computed regular product. -/
structure SemiclassicalMultiplicationDescent (C : RegularClosure h hL) : Prop where
  left : semiclassicalRelations C ≤ (rawSemiclassicalMultiplication C).ker
  right : semiclassicalRelations C ≤ (rawSemiclassicalMultiplication C).flip.ker

def semiclassicalMultiplication {C : RegularClosure h hL}
    (S : SemiclassicalMultiplicationDescent C) :
    Semiclassical C →ₗ[ℂ] Semiclassical C →ₗ[ℂ] Semiclassical C :=
  (rawSemiclassicalMultiplication C).liftQ₂ (semiclassicalRelations C)
    (semiclassicalRelations C) S.left S.right

/-- The quotient class of the geometric BG_m divided commutator. -/
def rawSemiclassicalBracket {C : RegularClosure h hL} (B : DividedCommutatorData C) :
    Regular H.moduli →ₗ[ℂ] Regular H.moduli →ₗ[ℂ] Semiclassical C :=
  (dividedCommutator B).compr₂ (semiclassicalRelations C).mkQ

/-- Descent is separate from antisymmetry, Jacobi and Leibniz laws. -/
structure SemiclassicalBracketDescent {C : RegularClosure h hL}
    (B : DividedCommutatorData C) : Prop where
  left : semiclassicalRelations C ≤ (rawSemiclassicalBracket B).ker
  right : semiclassicalRelations C ≤ (rawSemiclassicalBracket B).flip.ker

def semiclassicalBracket {C : RegularClosure h hL} {B : DividedCommutatorData C}
    (S : SemiclassicalBracketDescent B) :
    Semiclassical C →ₗ[ℂ] Semiclassical C →ₗ[ℂ] Semiclassical C :=
  (rawSemiclassicalBracket B).liftQ₂ (semiclassicalRelations C)
    (semiclassicalRelations C) S.left S.right

/-- The quotient map kills the literal image (L−1)H_reg. -/
theorem semiclassical_lefschetz (C : RegularClosure h hL) (a : Regular H.moduli) :
    (semiclassicalRelations C).mkQ (regularLefschetz C a) =
      (semiclassicalRelations C).mkQ a := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (Submodule.Quotient.mk_eq_zero (semiclassicalRelations C)).mpr ⟨a,rfl⟩

end MathlibExt.AlgebraicGeometry.HallSemiclassicalOperations
