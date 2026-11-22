/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.Shapes
public import MathlibExt.AlgebraicTopology.Quasicategory.InitialVertex
public import MathlibExt.AlgebraicTopology.SimplicialSet.GeneralJoinSliceOpposite
public import MathlibExt.CategoryTheory.NerveOppositeNaturality

/-!
# Canonical walking-span and coherent pushout-square shapes

The span is the universe-lifted standard walking span. Its terminal-object
completion is the full coherent diamond, with two triangles and their common
diagonal. The comparison with the opposite native pullback shapes is an
isomorphism of the entire ordinary nerves, with the actual inclusion retained.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace SSet.NativePushout

/-- The standard walking span at the original simplicial value universe. -/
abbrev SpanObjects := ULift.{u} WalkingSpan

/-- The native lifted category structure is the standard ULift category. -/
instance spanCategory : Category.{0} SpanObjects.{u} :=
  CategoryTheory.uliftCategory WalkingSpan

/-- The coherent diamond is the walking span with a terminal object adjoined. -/
abbrev DiamondObjects := WithTerminal SpanObjects.{u}

instance spanIsThin : Quiver.IsThin SpanObjects.{u} := fun x y => by
  change Subsingleton (x.down ⟶ y.down)
  infer_instance

instance diamondIsThin : Quiver.IsThin DiamondObjects.{u} := fun x y => by
  cases x with
  | star =>
    cases y with
    | star => change Subsingleton PUnit; infer_instance
    | of y => change Subsingleton PEmpty; infer_instance
  | of x =>
    cases y with
    | star => change Subsingleton PUnit; infer_instance
    | of y => change Subsingleton (x ⟶ y); exact spanIsThin x y

/-- The canonical inclusion into the terminal-object completion. -/
abbrev spanInclusionFunctor : SpanObjects.{u} ⥤ DiamondObjects.{u} := WithTerminal.incl

/-- The whole ordinary nerve of the walking span. -/
abbrev spanShape : SSet.{u} := nerve SpanObjects.{u}

/-- The whole ordinary nerve of the coherent diamond. -/
abbrev squareShape : SSet.{u} := nerve DiamondObjects.{u}

/-- The whole nerve map of the canonical span inclusion. -/
def spanInclusion : spanShape.{u} ⟶ squareShape.{u} := nerveMap spanInclusionFunctor

/-- An actual vertex of the canonical coherent square. -/
def point (v : DiamondObjects.{u}) : (Δ[0] : SSet.{u}) ⟶ squareShape.{u} :=
  yonedaEquiv.symm (ComposableArrows.mk₀ v)

/-- An actual square arrow, retaining all its simplicial degeneracies. -/
def edge {a b : DiamondObjects.{u}} (f : a ⟶ b) :
    (Δ[1] : SSet.{u}) ⟶ squareShape.{u} :=
  yonedaEquiv.symm (ComposableArrows.mk₁ f)

/-- The first branch of the original span, as the top side of the square. -/
def topEdge : (Δ[1] : SSet.{u}) ⟶ squareShape.{u} :=
  edge (WithTerminal.incl.map (show (ULift.up WalkingSpan.zero : SpanObjects.{u}) ⟶
    ULift.up WalkingSpan.left from WalkingSpan.Hom.fst))

/-- The second branch of the original span, as the left side of the square. -/
def leftEdge : (Δ[1] : SSet.{u}) ⟶ squareShape.{u} :=
  edge (WithTerminal.incl.map (show (ULift.up WalkingSpan.zero : SpanObjects.{u}) ⟶
    ULift.up WalkingSpan.right from WalkingSpan.Hom.snd))

/-- The first branch maps to the original adjoined terminal vertex. -/
def rightEdge : (Δ[1] : SSet.{u}) ⟶ squareShape.{u} :=
  edge (WithTerminal.homFrom (ULift.up WalkingSpan.left))

/-- The second branch maps to the same original terminal vertex. -/
def bottomEdge : (Δ[1] : SSet.{u}) ⟶ squareShape.{u} :=
  edge (WithTerminal.homFrom (ULift.up WalkingSpan.right))

/-- The common original diagonal from the span source to the terminal vertex. -/
def diagonal : (Δ[1] : SSet.{u}) ⟶ squareShape.{u} :=
  edge (WithTerminal.homFrom (ULift.up WalkingSpan.zero))

/-- The complete first triangle of the original coherent diamond. -/
def rightTriangle : (Δ[2] : SSet.{u}) ⟶ squareShape.{u} :=
  yonedaEquiv.symm (ComposableArrows.mk₂
    (WithTerminal.incl.map (show (ULift.up WalkingSpan.zero : SpanObjects.{u}) ⟶
      ULift.up WalkingSpan.left from WalkingSpan.Hom.fst))
    (WithTerminal.homFrom (ULift.up WalkingSpan.left)))

/-- The complete second triangle of the original coherent diamond. -/
def leftTriangle : (Δ[2] : SSet.{u}) ⟶ squareShape.{u} :=
  yonedaEquiv.symm (ComposableArrows.mk₂
    (WithTerminal.incl.map (show (ULift.up WalkingSpan.zero : SpanObjects.{u}) ⟶
      ULift.up WalkingSpan.right from WalkingSpan.Hom.snd))
    (WithTerminal.homFrom (ULift.up WalkingSpan.right)))

/-- The canonical opposite cospan functor keeps both original branch labels. -/
def cospanOppToSpan : NativePullback.CospanObjects.{u}ᵒᵖ ⥤ SpanObjects.{u} where
  obj x := ULift.up x.unop.down
  map {x y} f := by
    rcases x with ⟨⟨x⟩⟩
    rcases y with ⟨⟨y⟩⟩
    change WalkingSpan.Hom x y
    have g : WalkingCospan.Hom y x := f.unop
    cases g with
    | id _ => exact WalkingSpan.Hom.id _
    | term j => exact WidePushoutShape.Hom.init j
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The inverse functor keeps the same full original span arrows. -/
def spanToCospanOpp : SpanObjects.{u} ⥤ NativePullback.CospanObjects.{u}ᵒᵖ where
  obj x := op (ULift.up x.down)
  map {x y} f := by
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    change WalkingSpan.Hom x y at f
    change op (ULift.up x : NativePullback.CospanObjects.{u}) ⟶
      op (ULift.up y : NativePullback.CospanObjects.{u})
    cases f with
    | id _ => exact 𝟙 _
    | init j =>
      exact (show (ULift.up (some j) : NativePullback.CospanObjects.{u}) ⟶
        ULift.up WalkingCospan.one from WidePullbackShape.Hom.term j).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The whole opposite-cospan nerve is the whole original span nerve. -/
def cospanOppNerveIso : nerve NativePullback.CospanObjects.{u}ᵒᵖ ≅ spanShape.{u} where
  hom := nerveMap cospanOppToSpan
  inv := nerveMap spanToCospanOpp
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext i
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext i
    rfl

/-- The original opposite cospan shape is the actual walking-span shape. -/
def spanOppositeIso : NativePullback.cospanShape.{u}.op ≅ spanShape.{u} :=
  (nerveOppositeSimplicialIso NativePullback.CospanObjects.{u}).symm ≪≫ cospanOppNerveIso

/-- The opposite initial-object completion maps to the original terminal-object completion. -/
def squareOppToPushout : NativePullback.DiamondObjects.{u}ᵒᵖ ⥤ DiamondObjects.{u} :=
  (WithInitial.opEquiv (C := NativePullback.CospanObjects.{u})).functor ⋙
    WithTerminal.map cospanOppToSpan

/-- The inverse comparison keeps the actual original square category. -/
def squareToPullbackOpp : DiamondObjects.{u} ⥤ NativePullback.DiamondObjects.{u}ᵒᵖ :=
  WithTerminal.map spanToCospanOpp ⋙
    (WithInitial.opEquiv (C := NativePullback.CospanObjects.{u})).inverse

/-- The entire opposite-diamond nerve is the original pushout diamond nerve. -/
def squareOppNerveIso : nerve NativePullback.DiamondObjects.{u}ᵒᵖ ≅ squareShape.{u} where
  hom := nerveMap squareOppToPushout
  inv := nerveMap squareToPullbackOpp
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext i
    change squareToPullbackOpp.obj (squareOppToPushout.obj (s.obj i)) = s.obj i
    cases s.obj i with
    | op a => cases a <;> rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext i
    change squareOppToPushout.obj (squareToPullbackOpp.obj (s.obj i)) = s.obj i
    cases s.obj i <;> rfl

/-- The opposite of the whole original pullback diamond is the original pushout diamond. -/
def squareOppositeIso : NativePullback.squareShape.{u}.op ≅ squareShape.{u} :=
  (nerveOppositeSimplicialIso NativePullback.DiamondObjects.{u}).symm ≪≫ squareOppNerveIso

/-- The whole original cospan inclusion becomes the whole original span inclusion. -/
@[reassoc]
theorem op_cospanInclusion_comp_squareOppositeIso_hom :
    opFunctor.map NativePullback.cospanInclusion.{u} ≫ squareOppositeIso.hom =
      spanOppositeIso.hom ≫ spanInclusion := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  rfl

/-- Every original square point becomes its actual reversed square point. -/
theorem oppositePoint_comp_squareOppositeIso_hom (v : NativePullback.DiamondObjects.{u}) :
    oppositeVertex (NativePullback.point v) ≫ squareOppositeIso.hom =
      point (squareOppToPushout.obj (op v)) := by
  apply yonedaEquiv.injective
  unfold oppositeVertex
  rw [yonedaEquiv_comp, yonedaEquiv_opposite]
  apply nerve.ext_of_isThin
  funext i
  fin_cases i
  rfl

/-- Reversal identifies every original full square edge with its original opposite arrow. -/
theorem oppositeEdge_comp_squareOppositeIso_hom {a b : NativePullback.DiamondObjects.{u}}
    (f : a ⟶ b) :
    ((stdSimplex.opIso ⦋1⦌).inv ≫ opFunctor.map (NativePullback.edge f)) ≫
        squareOppositeIso.hom = edge (squareOppToPushout.map f.op) := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_opposite]
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The original initial point becomes the original adjoined terminal point. -/
theorem opposite_initialPoint_comp_squareOppositeIso_hom :
    oppositeVertex (NativePullback.point WithInitial.star) ≫ squareOppositeIso.{u}.hom =
      point WithTerminal.star :=
  oppositePoint_comp_squareOppositeIso_hom WithInitial.star

/-- The original top side reverses to the native pushout's right side. -/
theorem opposite_topEdge_comp_squareOppositeIso_hom :
    ((stdSimplex.opIso ⦋1⦌).inv ≫ opFunctor.map NativePullback.topEdge) ≫
      squareOppositeIso.{u}.hom = rightEdge :=
  oppositeEdge_comp_squareOppositeIso_hom
    (WithInitial.homTo (ULift.up WalkingCospan.left))

/-- The original left side reverses to the native pushout's bottom side. -/
theorem opposite_leftEdge_comp_squareOppositeIso_hom :
    ((stdSimplex.opIso ⦋1⦌).inv ≫ opFunctor.map NativePullback.leftEdge) ≫
      squareOppositeIso.{u}.hom = bottomEdge :=
  oppositeEdge_comp_squareOppositeIso_hom
    (WithInitial.homTo (ULift.up WalkingCospan.right))

/-- The original right side reverses to the native pushout's top side. -/
theorem opposite_rightEdge_comp_squareOppositeIso_hom :
    ((stdSimplex.opIso ⦋1⦌).inv ≫ opFunctor.map NativePullback.rightEdge) ≫
      squareOppositeIso.{u}.hom = topEdge :=
  oppositeEdge_comp_squareOppositeIso_hom
    (WithInitial.incl.map (show (ULift.up WalkingCospan.left : NativePullback.CospanObjects.{u}) ⟶
      ULift.up WalkingCospan.one from WalkingCospan.Hom.inl))

/-- The original bottom side reverses to the native pushout's left side. -/
theorem opposite_bottomEdge_comp_squareOppositeIso_hom :
    ((stdSimplex.opIso ⦋1⦌).inv ≫ opFunctor.map NativePullback.bottomEdge) ≫
      squareOppositeIso.{u}.hom = leftEdge :=
  oppositeEdge_comp_squareOppositeIso_hom
    (WithInitial.incl.map (show (ULift.up WalkingCospan.right : NativePullback.CospanObjects.{u}) ⟶
      ULift.up WalkingCospan.one from WalkingCospan.Hom.inr))

/-- The source point of the span remains the common source of both full triangles. -/
theorem rightTriangle_initial :
    stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋2⦌ 0) ≫ rightTriangle.{u} =
      point (WithTerminal.of (ULift.up WalkingSpan.zero)) := by
  apply yonedaEquiv.injective
  rw [← yonedaEquiv_naturality]
  apply nerve.ext_of_isThin
  funext i
  fin_cases i
  rfl

/-- The first complete triangle contains the original top side. -/
theorem rightTriangle_topEdge : stdSimplex.δ (2 : Fin 3) ≫ rightTriangle.{u} = topEdge := by
  apply yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp]
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The second complete triangle contains the original left side. -/
theorem leftTriangle_leftEdge : stdSimplex.δ (2 : Fin 3) ≫ leftTriangle.{u} = leftEdge := by
  apply yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp]
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The first complete triangle contains the original right side. -/
theorem rightTriangle_rightEdge : stdSimplex.δ (0 : Fin 3) ≫ rightTriangle.{u} = rightEdge := by
  apply yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp]
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The second complete triangle contains the original bottom side. -/
theorem leftTriangle_bottomEdge : stdSimplex.δ (0 : Fin 3) ≫ leftTriangle.{u} = bottomEdge := by
  apply yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp]
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The first complete triangle contains the full common diagonal. -/
theorem rightTriangle_diagonal : stdSimplex.δ (1 : Fin 3) ≫ rightTriangle.{u} = diagonal := by
  apply yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp]
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The second complete triangle contains the same full common diagonal. -/
theorem leftTriangle_diagonal : stdSimplex.δ (1 : Fin 3) ≫ leftTriangle.{u} = diagonal := by
  apply yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp]
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

end SSet.NativePushout

namespace SSet.NativePushout

/-- The actual cospan at the original terminal square vertex. -/
def cospanInSquare : NativePullback.CospanObjects.{u} ⥤ DiamondObjects.{u} :=
  ULift.downFunctor ⋙ cospan (WithTerminal.homFrom (ULift.up WalkingSpan.left))
    (WithTerminal.homFrom (ULift.up WalkingSpan.right))

/-- The original initial-object completion maps to the same oriented terminal-object completion. -/
def squareFromPullbackFunctor : NativePullback.DiamondObjects.{u} ⥤ DiamondObjects.{u} :=
  WithInitial.lift (Z := WithTerminal.of (ULift.up WalkingSpan.zero)) cospanInSquare
    (fun v => by
      rcases v with ⟨v⟩
      cases v with
      | none => exact WithTerminal.homFrom (ULift.up WalkingSpan.zero)
      | some v =>
        cases v
        · exact WithTerminal.incl.map (show
            (ULift.up WalkingSpan.zero : SpanObjects.{u}) ⟶ ULift.up WalkingSpan.left from
              WalkingSpan.Hom.fst)
        · exact WithTerminal.incl.map (show
            (ULift.up WalkingSpan.zero : SpanObjects.{u}) ⟶ ULift.up WalkingSpan.right from
              WalkingSpan.Hom.snd))
    (fun _ _ _ => Subsingleton.elim _ _)

/-- The actual span at the original initial square vertex. -/
def spanInPullbackSquare : SpanObjects.{u} ⥤ NativePullback.DiamondObjects.{u} :=
  ULift.downFunctor ⋙ span (WithInitial.homTo (ULift.up WalkingCospan.left))
    (WithInitial.homTo (ULift.up WalkingCospan.right))

/-- The same oriented square maps back to the original initial-object completion. -/
def squareToPullbackFunctor : DiamondObjects.{u} ⥤ NativePullback.DiamondObjects.{u} :=
  WithTerminal.lift (Z := WithInitial.of (ULift.up WalkingCospan.one)) spanInPullbackSquare
    (fun v => by
      rcases v with ⟨v⟩
      cases v with
      | none => exact WithInitial.homTo (ULift.up WalkingCospan.one)
      | some v =>
        cases v
        · exact WithInitial.incl.map (show
            (ULift.up WalkingCospan.left : NativePullback.CospanObjects.{u}) ⟶
              ULift.up WalkingCospan.one from WalkingCospan.Hom.inl)
        · exact WithInitial.incl.map (show
            (ULift.up WalkingCospan.right : NativePullback.CospanObjects.{u}) ⟶
              ULift.up WalkingCospan.one from WalkingCospan.Hom.inr))
    (fun _ _ _ => Subsingleton.elim _ _)

/-- Both native diamond shapes are the same oriented whole coherent square. -/
def squareIso : NativePullback.squareShape.{u} ≅ squareShape.{u} where
  hom := nerveMap squareFromPullbackFunctor
  inv := nerveMap squareToPullbackFunctor
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext i
    change squareToPullbackFunctor.obj (squareFromPullbackFunctor.obj (s.obj i)) = s.obj i
    cases s.obj i with
    | star => rfl
    | of v =>
      rcases v with ⟨v⟩
      cases v with
      | none => rfl
      | some v => cases v <;> rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext i
    change squareFromPullbackFunctor.obj (squareToPullbackFunctor.obj (s.obj i)) = s.obj i
    cases s.obj i with
    | star => rfl
    | of v =>
      rcases v with ⟨v⟩
      cases v with
      | none => rfl
      | some v => cases v <;> rfl

/-- The original top side agrees in both native square presentations. -/
theorem topEdge_comp_squareIso_hom : NativePullback.topEdge.{u} ≫ squareIso.hom = topEdge := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The original left side agrees in both native square presentations. -/
theorem leftEdge_comp_squareIso_hom : NativePullback.leftEdge.{u} ≫ squareIso.hom = leftEdge := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The original right side agrees in both native square presentations. -/
theorem rightEdge_comp_squareIso_hom :
    NativePullback.rightEdge.{u} ≫ squareIso.hom = rightEdge := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The original bottom side agrees in both native square presentations. -/
theorem bottomEdge_comp_squareIso_hom :
    NativePullback.bottomEdge.{u} ≫ squareIso.hom = bottomEdge := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

end SSet.NativePushout
