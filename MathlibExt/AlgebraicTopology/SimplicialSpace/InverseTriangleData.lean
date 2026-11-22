/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.FixedEdgeTriangleCoherence
import MathlibExt.AlgebraicTopology.SimplicialSpace.AdjacentTriangleGluing

/-!
# Original left, right and paired inverse-triangle data

These are raw chosen pullbacks for an arbitrary simplicial space. The right
triangle fixes its first edge and the left triangle fixes its last edge, using
the same prescribed arrow. Their varying inverse candidates remain independent.

This is the common definitional inverse-triangle geometry used in Rezk (2001),
Section 11. Fibrancy, Segalness and semantic inverse assertions are separate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

namespace SimplicialSpace.InverseTriangle

open SegalHomotopy

/-- The original identity vertex, as its actual Yoneda point. -/
def identityPoint (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    (Δ[0] : SSet.{u}) ⟶ mappingFibre W x x :=
  SSet.yonedaEquiv.symm (identityVertex W x)

/-- The identity point's whole original W1 projection is the degeneracy of x. -/
@[reassoc]
theorem identityPoint_fst (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    identityPoint W x ≫ mappingFibre.fst W x x =
      SSet.yonedaEquiv.symm x ≫ W.diagram.σ (0 : Fin 1) := by
  apply SSet.yonedaEquiv.injective
  simp only [identityPoint, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
    identityVertex_fst]

/-- The identity point retains the native Delta0 projection. -/
@[reassoc (attr := simp)]
theorem identityPoint_snd (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    identityPoint W x ≫ mappingFibre.snd W x x = 𝟙 _ :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- Identity points move along the actual prescribed-vertex fibre map. -/
@[reassoc]
theorem identityPoint_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    {x : (W.diagram _⦋0⦌) _⦋0⦌} {x' : (V.diagram _⦋0⦌) _⦋0⦌}
    (hx : mappingVertexMap q x = x') :
    identityPoint W x ≫ mappingFibre.map q hx hx = identityPoint V x' := by
  apply pullback.hom_ext (f := mappingEndpoint V) (g := mappingPointPair V x' x')
  · change (identityPoint W x ≫ mappingFibre.map q hx hx) ≫ mappingFibre.fst V x' x' =
      identityPoint V x' ≫ mappingFibre.fst V x' x'
    simp only [Category.assoc, mappingFibre.map_fst, identityPoint_fst,
      identityPoint_fst_assoc]
    rw [SimplicialObject.σ_naturality q.hom (0 : Fin 1),
      ← Category.assoc, SSet.yonedaEquiv_symm_comp]
    change SSet.yonedaEquiv.symm (mappingVertexMap q x) ≫ V.diagram.σ (0 : Fin 1) = _
    rw [hx]
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

variable (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌)
  (f : (mappingFibre W x y) _⦋0⦌)

/-- The middle of the original triangle with first edge f and varying last edge c. -/
def rightMiddle : FixedEdgeTriangle.rightTriangle W x y f ⟶ mappingFibre W x x :=
  FixedEdgeTriangle.rightTriangleProjection W x y f ≫ triangleMiddle W x y x

/-- The middle of the original triangle with varying first edge b and last edge f. -/
def leftMiddle : FixedEdgeTriangle.leftTriangle W x y f ⟶ mappingFibre W y y :=
  FixedEdgeTriangle.leftTriangleProjection W x y f ≫ triangleMiddle W y x y

/-- The literal strict right inverse-triangle pullback over the identity at x. -/
abbrev rightSpace : SSet.{u} := pullback (rightMiddle W x y f) (identityPoint W x)

/-- The literal strict left inverse-triangle pullback over the identity at y. -/
abbrev leftSpace : SSet.{u} := pullback (leftMiddle W x y f) (identityPoint W y)

/-- The native first projection to the original fixed-first triangle space. -/
abbrev rightToFixed : rightSpace W x y f ⟶ FixedEdgeTriangle.rightTriangle W x y f :=
  pullback.fst _ _

/-- The native Delta0 projection of the right strict pullback. -/
abbrev rightToPoint : rightSpace W x y f ⟶ (Δ[0] : SSet.{u}) := pullback.snd _ _

/-- The native first projection to the original fixed-last triangle space. -/
abbrev leftToFixed : leftSpace W x y f ⟶ FixedEdgeTriangle.leftTriangle W x y f :=
  pullback.fst _ _

/-- The native Delta0 projection of the left strict pullback. -/
abbrev leftToPoint : leftSpace W x y f ⟶ (Δ[0] : SSet.{u}) := pullback.snd _ _

/-- The whole original x,y,x triangle in the right strict space. -/
def rightTriangle : rightSpace W x y f ⟶ triangleSpace W x y x :=
  rightToFixed W x y f ≫ FixedEdgeTriangle.rightTriangleProjection W x y f

/-- The independently varying original last edge c:y to x. -/
def rightCandidate : rightSpace W x y f ⟶ mappingFibre W y x :=
  rightToFixed W x y f ≫ FixedEdgeTriangle.rightProjection W x y f

/-- The whole original y,x,y triangle in the left strict space. -/
def leftTriangle : leftSpace W x y f ⟶ triangleSpace W y x y :=
  leftToFixed W x y f ≫ FixedEdgeTriangle.leftTriangleProjection W x y f

/-- The independently varying original first edge b:y to x. -/
def leftCandidate : leftSpace W x y f ⟶ mappingFibre W y x :=
  leftToFixed W x y f ≫ FixedEdgeTriangle.leftProjection W x y f

/-- Both actual native projections form the right strict pullback square. -/
theorem right_isPullback : IsPullback (rightToFixed W x y f) (rightToPoint W x y f)
    (rightMiddle W x y f) (identityPoint W x) :=
  IsPullback.of_hasPullback _ _

/-- Both actual native projections form the left strict pullback square. -/
theorem left_isPullback : IsPullback (leftToFixed W x y f) (leftToPoint W x y f)
    (leftMiddle W x y f) (identityPoint W y) :=
  IsPullback.of_hasPullback _ _

/-- The whole middle of the right original triangle is the identity point. -/
@[reassoc]
theorem right_middle : rightTriangle W x y f ≫ triangleMiddle W x y x =
    rightToPoint W x y f ≫ identityPoint W x := by
  change (rightToFixed W x y f ≫ FixedEdgeTriangle.rightTriangleProjection W x y f) ≫
    triangleMiddle W x y x = _
  rw [Category.assoc]
  exact pullback.condition (f := rightMiddle W x y f) (g := identityPoint W x)

/-- The whole middle of the left original triangle is the identity point. -/
@[reassoc]
theorem left_middle : leftTriangle W x y f ≫ triangleMiddle W y x y =
    leftToPoint W x y f ≫ identityPoint W y := by
  change (leftToFixed W x y f ≫ FixedEdgeTriangle.leftTriangleProjection W x y f) ≫
    triangleMiddle W y x y = _
  rw [Category.assoc]
  exact pullback.condition (f := leftMiddle W x y f) (g := identityPoint W y)

/-- The right triangle retains its original fixed-first comparison square. -/
@[reassoc]
theorem right_comparison : rightTriangle W x y f ≫ triangleComparison W x y x =
    rightCandidate W x y f ≫ FixedEdgeTriangle.rightPair W x y f := by
  simp only [rightTriangle, rightCandidate, Category.assoc,
    (FixedEdgeTriangle.rightGeometry W x y f).2.1]

/-- The left triangle retains its original fixed-last comparison square. -/
@[reassoc]
theorem left_comparison : leftTriangle W x y f ≫ triangleComparison W y x y =
    leftCandidate W x y f ≫ FixedEdgeTriangle.leftPair W x y f := by
  simp only [leftTriangle, leftCandidate, Category.assoc,
    (FixedEdgeTriangle.leftGeometry W x y f).2.1]

/-- The right triangle's first edge is the same prescribed f, in every degree. -/
@[reassoc]
theorem right_fixedFirst : rightTriangle W x y f ≫ triangleComparison W x y x ≫ prod.fst =
    rightToPoint W x y f ≫ SSet.yonedaEquiv.symm f := by
  rw [← Category.assoc, right_comparison, Category.assoc,
    (FixedEdgeTriangle.rightPairLaws W x y f).1]
  have h : rightCandidate W x y f ≫ mappingFibre.snd W y x = rightToPoint W x y f :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [← Category.assoc, h]

/-- The left triangle's last edge is that same prescribed f, in every degree. -/
@[reassoc]
theorem left_fixedLast : leftTriangle W x y f ≫ triangleComparison W y x y ≫ prod.snd =
    leftToPoint W x y f ≫ SSet.yonedaEquiv.symm f := by
  rw [← Category.assoc, left_comparison, Category.assoc,
    (FixedEdgeTriangle.leftPairLaws W x y f).2]
  have h : leftCandidate W x y f ≫ mappingFibre.snd W y x = leftToPoint W x y f :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [← Category.assoc, h]

/-- The right triangle's last edge is exactly its independent candidate c. -/
@[reassoc]
theorem right_varyingLast : rightTriangle W x y f ≫ triangleComparison W x y x ≫ prod.snd =
    rightCandidate W x y f := by
  rw [← Category.assoc, right_comparison, Category.assoc,
    (FixedEdgeTriangle.rightPairLaws W x y f).2, Category.comp_id]

/-- The left triangle's first edge is exactly its independent candidate b. -/
@[reassoc]
theorem left_varyingFirst : leftTriangle W x y f ≫ triangleComparison W y x y ≫ prod.fst =
    leftCandidate W x y f := by
  rw [← Category.assoc, left_comparison, Category.assoc,
    (FixedEdgeTriangle.leftPairLaws W x y f).1, Category.comp_id]

/-- The right fixed edge retains its original W1 face. -/
@[reassoc]
theorem right_firstFace : rightTriangle W x y f ≫ triangleProjection W x y x ≫
    W.diagram.δ (2 : Fin 3) =
      rightToPoint W x y f ≫ SSet.yonedaEquiv.symm f ≫ mappingFibre.fst W x y := by
  rw [triangleProjection_first, right_fixedFirst_assoc]

/-- The right varying edge retains its original W1 face. -/
@[reassoc]
theorem right_lastFace : rightTriangle W x y f ≫ triangleProjection W x y x ≫
    W.diagram.δ (0 : Fin 3) = rightCandidate W x y f ≫ mappingFibre.fst W y x := by
  rw [triangleProjection_last, right_varyingLast_assoc]

/-- The left varying edge retains its original W1 face. -/
@[reassoc]
theorem left_firstFace : leftTriangle W x y f ≫ triangleProjection W y x y ≫
    W.diagram.δ (2 : Fin 3) = leftCandidate W x y f ≫ mappingFibre.fst W y x := by
  rw [triangleProjection_first, left_varyingFirst_assoc]

/-- The left fixed edge retains its original W1 face. -/
@[reassoc]
theorem left_lastFace : leftTriangle W x y f ≫ triangleProjection W y x y ≫
    W.diagram.δ (0 : Fin 3) =
      leftToPoint W x y f ≫ SSet.yonedaEquiv.symm f ≫ mappingFibre.fst W x y := by
  rw [triangleProjection_last, left_fixedLast_assoc]

/-- The two spaces form the literal ordered product I_L(f) times I_R(f). -/
abbrev pairedSpace : SSet.{u} := leftSpace W x y f ⨯ rightSpace W x y f

/-- The first factor is the original left strict space. -/
abbrev pairedLeft : pairedSpace W x y f ⟶ leftSpace W x y f := prod.fst

/-- The second factor is the original right strict space. -/
abbrev pairedRight : pairedSpace W x y f ⟶ rightSpace W x y f := prod.snd

/-- The paired space's point projection uses its original left factor. -/
def pairedToPoint : pairedSpace W x y f ⟶ (Δ[0] : SSet.{u}) :=
  pairedLeft W x y f ≫ leftToPoint W x y f

/-- The same original point projection is obtained from the right factor. -/
@[reassoc]
theorem pairedToPoint_right : pairedRight W x y f ≫ rightToPoint W x y f =
    pairedToPoint W x y f :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The ordered pair of independent original candidates is (b,c), with no equality imposed. -/
def pairedCandidates : pairedSpace W x y f ⟶ mappingFibre W y x ⨯ mappingFibre W y x :=
  prod.map (leftCandidate W x y f) (rightCandidate W x y f)

/-- The candidate pair's first projection is the left candidate b. -/
@[reassoc (attr := simp)]
theorem pairedCandidates_fst : pairedCandidates W x y f ≫ prod.fst =
    pairedLeft W x y f ≫ leftCandidate W x y f := prod.map_fst _ _

/-- The candidate pair's second projection is the right candidate c. -/
@[reassoc (attr := simp)]
theorem pairedCandidates_snd : pairedCandidates W x y f ≫ prod.snd =
    pairedRight W x y f ≫ rightCandidate W x y f := prod.map_snd _ _

section Moving

variable {W V : SimplicialSpace.{u}} (q : W ⟶ V)
  {x y : (W.diagram _⦋0⦌) _⦋0⦌} {x' y' : (V.diagram _⦋0⦌) _⦋0⦌}
  {f : (mappingFibre W x y) _⦋0⦌} {f' : (mappingFibre V x' y') _⦋0⦌}
  (hx : mappingVertexMap q x = x') (hy : mappingVertexMap q y = y')
  (hf : (mappingFibre.map q hx hy).app (op ⦋0⦌) f = f')

/-- The original middle face moves along both actual mapping-fibre projections. -/
@[reassoc]
theorem triangleMiddle_natural
    {z : (W.diagram _⦋0⦌) _⦋0⦌} {z' : (V.diagram _⦋0⦌) _⦋0⦌}
    (hz : mappingVertexMap q z = z') :
    AdjacentTriangle.triangleMap q hx hy hz ≫ triangleMiddle V x' y' z' =
      triangleMiddle W x y z ≫ mappingFibre.map q hx hz := by
  apply pullback.hom_ext (f := mappingEndpoint V) (g := mappingPointPair V x' z')
  · change (AdjacentTriangle.triangleMap q hx hy hz ≫ triangleMiddle V x' y' z') ≫
      mappingFibre.fst V x' z' =
        (triangleMiddle W x y z ≫ mappingFibre.map q hx hz) ≫ mappingFibre.fst V x' z'
    simp only [Category.assoc, triangleMiddle_fst, triangleMiddle_fst_assoc,
      AdjacentTriangle.triangleMap_projection_assoc, mappingFibre.map_fst]
    rw [← SimplicialObject.δ_naturality q.hom (1 : Fin 3)]
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

include hf in
/-- The fixed-first pair uses the same moved f and the original independent candidate map. -/
@[reassoc]
theorem rightPair_natural :
    FixedEdgeTriangle.rightPair W x y f ≫
        prod.map (mappingFibre.map q hx hy) (mappingFibre.map q hy hx) =
      mappingFibre.map q hy hx ≫ FixedEdgeTriangle.rightPair V x' y' f' := by
  have hp : SSet.yonedaEquiv.symm f ≫ mappingFibre.map q hx hy =
      SSet.yonedaEquiv.symm f' := by
    rw [SSet.yonedaEquiv_symm_comp]
    rw [hf]
  apply prod.hom_ext
  · rw [Category.assoc, prod.map_fst, ← Category.assoc,
      (FixedEdgeTriangle.rightPairLaws W x y f).1, Category.assoc, hp,
      Category.assoc, (FixedEdgeTriangle.rightPairLaws V x' y' f').1,
      ← Category.assoc, mappingFibre.map_snd]
  · rw [Category.assoc, prod.map_snd, ← Category.assoc,
      (FixedEdgeTriangle.rightPairLaws W x y f).2, Category.id_comp,
      Category.assoc, (FixedEdgeTriangle.rightPairLaws V x' y' f').2, Category.comp_id]

include hf in
/-- The fixed-last pair uses that same moved f and the original independent candidate map. -/
@[reassoc]
theorem leftPair_natural :
    FixedEdgeTriangle.leftPair W x y f ≫
        prod.map (mappingFibre.map q hy hx) (mappingFibre.map q hx hy) =
      mappingFibre.map q hy hx ≫ FixedEdgeTriangle.leftPair V x' y' f' := by
  have hp : SSet.yonedaEquiv.symm f ≫ mappingFibre.map q hx hy =
      SSet.yonedaEquiv.symm f' := by
    rw [SSet.yonedaEquiv_symm_comp]
    rw [hf]
  apply prod.hom_ext
  · rw [Category.assoc, prod.map_fst, ← Category.assoc,
      (FixedEdgeTriangle.leftPairLaws W x y f).1, Category.id_comp,
      Category.assoc, (FixedEdgeTriangle.leftPairLaws V x' y' f').1, Category.comp_id]
  · rw [Category.assoc, prod.map_snd, ← Category.assoc,
      (FixedEdgeTriangle.leftPairLaws W x y f).2, Category.assoc, hp,
      Category.assoc, (FixedEdgeTriangle.leftPairLaws V x' y' f').2,
      ← Category.assoc, mappingFibre.map_snd]

/-- Transport the actual fixed-first triangle, retaining its whole original triangle and c. -/
def rightFixedMap : FixedEdgeTriangle.rightTriangle W x y f ⟶
    FixedEdgeTriangle.rightTriangle V x' y' f' :=
  pullback.lift
    (FixedEdgeTriangle.rightTriangleProjection W x y f ≫
      AdjacentTriangle.triangleMap q hx hy hx)
    (FixedEdgeTriangle.rightProjection W x y f ≫ mappingFibre.map q hy hx) (by
      calc
        (FixedEdgeTriangle.rightTriangleProjection W x y f ≫
            AdjacentTriangle.triangleMap q hx hy hx) ≫ triangleComparison V x' y' x' =
            FixedEdgeTriangle.rightTriangleProjection W x y f ≫ triangleComparison W x y x ≫
              prod.map (mappingFibre.map q hx hy) (mappingFibre.map q hy hx) := by
                rw [Category.assoc, AdjacentTriangle.triangleMap_edges]
        _ = (FixedEdgeTriangle.rightProjection W x y f ≫ FixedEdgeTriangle.rightPair W x y f) ≫
              prod.map (mappingFibre.map q hx hy) (mappingFibre.map q hy hx) := by
                rw [← Category.assoc, (FixedEdgeTriangle.rightGeometry W x y f).2.1]
        _ = (FixedEdgeTriangle.rightProjection W x y f ≫ mappingFibre.map q hy hx) ≫
              FixedEdgeTriangle.rightPair V x' y' f' := by
                rw [Category.assoc, rightPair_natural q hx hy hf, ← Category.assoc])

/-- Transport the actual fixed-last triangle, retaining its whole original triangle and b. -/
def leftFixedMap : FixedEdgeTriangle.leftTriangle W x y f ⟶
    FixedEdgeTriangle.leftTriangle V x' y' f' :=
  pullback.lift
    (FixedEdgeTriangle.leftTriangleProjection W x y f ≫
      AdjacentTriangle.triangleMap q hy hx hy)
    (FixedEdgeTriangle.leftProjection W x y f ≫ mappingFibre.map q hy hx) (by
      calc
        (FixedEdgeTriangle.leftTriangleProjection W x y f ≫
            AdjacentTriangle.triangleMap q hy hx hy) ≫ triangleComparison V y' x' y' =
            FixedEdgeTriangle.leftTriangleProjection W x y f ≫ triangleComparison W y x y ≫
              prod.map (mappingFibre.map q hy hx) (mappingFibre.map q hx hy) := by
                rw [Category.assoc, AdjacentTriangle.triangleMap_edges]
        _ = (FixedEdgeTriangle.leftProjection W x y f ≫ FixedEdgeTriangle.leftPair W x y f) ≫
              prod.map (mappingFibre.map q hy hx) (mappingFibre.map q hx hy) := by
                rw [← Category.assoc, (FixedEdgeTriangle.leftGeometry W x y f).2.1]
        _ = (FixedEdgeTriangle.leftProjection W x y f ≫ mappingFibre.map q hy hx) ≫
              FixedEdgeTriangle.leftPair V x' y' f' := by
                rw [Category.assoc, leftPair_natural q hx hy hf, ← Category.assoc])

/-- The fixed-first transport retains the original whole AdjacentTriangle map. -/
@[reassoc (attr := simp)]
theorem rightFixedMap_triangle : rightFixedMap q hx hy hf ≫
    FixedEdgeTriangle.rightTriangleProjection V x' y' f' =
      FixedEdgeTriangle.rightTriangleProjection W x y f ≫
        AdjacentTriangle.triangleMap q hx hy hx := pullback.lift_fst _ _ _

/-- The fixed-first transport retains the original varying c map. -/
@[reassoc (attr := simp)]
theorem rightFixedMap_candidate : rightFixedMap q hx hy hf ≫
    FixedEdgeTriangle.rightProjection V x' y' f' =
      FixedEdgeTriangle.rightProjection W x y f ≫ mappingFibre.map q hy hx :=
  pullback.lift_snd _ _ _

/-- The fixed-last transport retains the original whole AdjacentTriangle map. -/
@[reassoc (attr := simp)]
theorem leftFixedMap_triangle : leftFixedMap q hx hy hf ≫
    FixedEdgeTriangle.leftTriangleProjection V x' y' f' =
      FixedEdgeTriangle.leftTriangleProjection W x y f ≫
        AdjacentTriangle.triangleMap q hy hx hy := pullback.lift_fst _ _ _

/-- The fixed-last transport retains the original varying b map. -/
@[reassoc (attr := simp)]
theorem leftFixedMap_candidate : leftFixedMap q hx hy hf ≫
    FixedEdgeTriangle.leftProjection V x' y' f' =
      FixedEdgeTriangle.leftProjection W x y f ≫ mappingFibre.map q hy hx :=
  pullback.lift_snd _ _ _

/-- The original right middle moves along the identity-endpoint fibre map. -/
@[reassoc]
theorem rightMiddle_natural : rightFixedMap q hx hy hf ≫ rightMiddle V x' y' f' =
    rightMiddle W x y f ≫ mappingFibre.map q hx hx := by
  simp only [rightMiddle, Category.assoc, rightFixedMap_triangle_assoc,
    triangleMiddle_natural]

/-- The original left middle moves along its other identity-endpoint fibre map. -/
@[reassoc]
theorem leftMiddle_natural : leftFixedMap q hx hy hf ≫ leftMiddle V x' y' f' =
    leftMiddle W x y f ≫ mappingFibre.map q hy hy := by
  simp only [leftMiddle, Category.assoc, leftFixedMap_triangle_assoc,
    triangleMiddle_natural]

/-- The original right strict space map, with the same moved f and both prescribed projections. -/
def rightMap : rightSpace W x y f ⟶ rightSpace V x' y' f' :=
  pullback.lift (rightToFixed W x y f ≫ rightFixedMap q hx hy hf) (rightToPoint W x y f) (by
    calc
      (rightToFixed W x y f ≫ rightFixedMap q hx hy hf) ≫ rightMiddle V x' y' f' =
          rightToFixed W x y f ≫ rightMiddle W x y f ≫ mappingFibre.map q hx hx := by
            rw [Category.assoc, rightMiddle_natural]
      _ = (rightToPoint W x y f ≫ identityPoint W x) ≫ mappingFibre.map q hx hx := by
            rw [← Category.assoc, pullback.condition]
      _ = rightToPoint W x y f ≫ identityPoint V x' := by
            rw [Category.assoc, identityPoint_natural q hx])

/-- The original left strict space map uses that same moved f, with its other identity endpoint. -/
def leftMap : leftSpace W x y f ⟶ leftSpace V x' y' f' :=
  pullback.lift (leftToFixed W x y f ≫ leftFixedMap q hx hy hf) (leftToPoint W x y f) (by
    calc
      (leftToFixed W x y f ≫ leftFixedMap q hx hy hf) ≫ leftMiddle V x' y' f' =
          leftToFixed W x y f ≫ leftMiddle W x y f ≫ mappingFibre.map q hy hy := by
            rw [Category.assoc, leftMiddle_natural]
      _ = (leftToPoint W x y f ≫ identityPoint W y) ≫ mappingFibre.map q hy hy := by
            rw [← Category.assoc, pullback.condition]
      _ = leftToPoint W x y f ≫ identityPoint V y' := by
            rw [Category.assoc, identityPoint_natural q hy])

/-- The right strict map preserves the actual native first projection. -/
@[reassoc (attr := simp)]
theorem rightMap_fixed : rightMap q hx hy hf ≫ rightToFixed V x' y' f' =
    rightToFixed W x y f ≫ rightFixedMap q hx hy hf := pullback.lift_fst _ _ _

/-- The right strict map preserves the actual native Delta0 projection. -/
@[reassoc (attr := simp)]
theorem rightMap_point : rightMap q hx hy hf ≫ rightToPoint V x' y' f' =
    rightToPoint W x y f := pullback.lift_snd _ _ _

/-- The left strict map preserves the actual native first projection. -/
@[reassoc (attr := simp)]
theorem leftMap_fixed : leftMap q hx hy hf ≫ leftToFixed V x' y' f' =
    leftToFixed W x y f ≫ leftFixedMap q hx hy hf := pullback.lift_fst _ _ _

/-- The left strict map preserves the actual native Delta0 projection. -/
@[reassoc (attr := simp)]
theorem leftMap_point : leftMap q hx hy hf ≫ leftToPoint V x' y' f' =
    leftToPoint W x y f := pullback.lift_snd _ _ _

/-- The right strict map retains the whole original triangle transport. -/
@[reassoc (attr := simp)]
theorem rightMap_triangle : rightMap q hx hy hf ≫ rightTriangle V x' y' f' =
    rightTriangle W x y f ≫ AdjacentTriangle.triangleMap q hx hy hx := by
  simp only [rightTriangle, Category.assoc, rightMap_fixed_assoc, rightFixedMap_triangle]

/-- The right strict map retains the independently varying original candidate c. -/
@[reassoc (attr := simp)]
theorem rightMap_candidate : rightMap q hx hy hf ≫ rightCandidate V x' y' f' =
    rightCandidate W x y f ≫ mappingFibre.map q hy hx := by
  simp only [rightCandidate, Category.assoc, rightMap_fixed_assoc, rightFixedMap_candidate]

/-- The left strict map retains the whole original triangle transport. -/
@[reassoc (attr := simp)]
theorem leftMap_triangle : leftMap q hx hy hf ≫ leftTriangle V x' y' f' =
    leftTriangle W x y f ≫ AdjacentTriangle.triangleMap q hy hx hy := by
  simp only [leftTriangle, Category.assoc, leftMap_fixed_assoc, leftFixedMap_triangle]

/-- The left strict map retains the independently varying original candidate b. -/
@[reassoc (attr := simp)]
theorem leftMap_candidate : leftMap q hx hy hf ≫ leftCandidate V x' y' f' =
    leftCandidate W x y f ≫ mappingFibre.map q hy hx := by
  simp only [leftCandidate, Category.assoc, leftMap_fixed_assoc, leftFixedMap_candidate]

/-- Both strict spaces move by the product of the same-f maps, in left/right order. -/
def pairedMap : pairedSpace W x y f ⟶ pairedSpace V x' y' f' :=
  prod.map (leftMap q hx hy hf) (rightMap q hx hy hf)

/-- The paired transport preserves its original left factor. -/
@[reassoc (attr := simp)]
theorem pairedMap_left : pairedMap q hx hy hf ≫ pairedLeft V x' y' f' =
    pairedLeft W x y f ≫ leftMap q hx hy hf := prod.map_fst _ _

/-- The paired transport preserves its original right factor. -/
@[reassoc (attr := simp)]
theorem pairedMap_right : pairedMap q hx hy hf ≫ pairedRight V x' y' f' =
    pairedRight W x y f ≫ rightMap q hx hy hf := prod.map_snd _ _

/-- The paired transport retains the actual common Delta0 point. -/
@[reassoc (attr := simp)]
theorem pairedMap_point : pairedMap q hx hy hf ≫ pairedToPoint V x' y' f' =
    pairedToPoint W x y f := by
  simp only [pairedToPoint, pairedMap_left_assoc, leftMap_point]

/-- Both independent candidates move along the same original fibre map, with no equality imposed. -/
@[reassoc]
theorem pairedMap_candidates : pairedMap q hx hy hf ≫ pairedCandidates V x' y' f' =
    pairedCandidates W x y f ≫ prod.map (mappingFibre.map q hy hx) (mappingFibre.map q hy hx) := by
  apply prod.hom_ext
  · simp only [Category.assoc, pairedCandidates_fst, pairedCandidates_fst_assoc,
      pairedMap_left_assoc, leftMap_candidate, prod.map_fst]
  · simp only [Category.assoc, pairedCandidates_snd, pairedCandidates_snd_assoc,
      pairedMap_right_assoc, rightMap_candidate, prod.map_snd]

end Moving

section Functoriality

private theorem triangle_transport_id (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    AdjacentTriangle.triangleMap (𝟙 W) (x := x) (y := y) (z := z)
      (x' := x) (y' := y) (z' := z) rfl rfl rfl = 𝟙 _ := by
  apply pullback.hom_ext
  · simpa only [triangleProjection, Category.id_comp] using
      (AdjacentTriangle.triangleMap_projection (𝟙 W) (x := x) (y := y) (z := z)
        (x' := x) (y' := y) (z' := z) rfl rfl rfl).trans (Category.comp_id _)
  · change AdjacentTriangle.triangleMap (𝟙 W) (x := x) (y := y) (z := z)
      (x' := x) (y' := y) (z' := z) rfl rfl rfl ≫ triangleComparison W x y z =
        𝟙 _ ≫ triangleComparison W x y z
    rw [AdjacentTriangle.triangleMap_edges (𝟙 W) (x := x) (y := y) (z := z)
      (x' := x) (y' := y) (z' := z) rfl rfl rfl, mappingFibre.map_id W x y,
      mappingFibre.map_id W y z]
    apply prod.hom_ext
    · simp only [Category.assoc, prod.map_fst, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, prod.map_snd, Category.comp_id, Category.id_comp]

private theorem triangle_transport_comp {W V U : SimplicialSpace.{u}} (q : W ⟶ V) (r : V ⟶ U)
    {x y z : (W.diagram _⦋0⦌) _⦋0⦌} {x' y' z' : (V.diagram _⦋0⦌) _⦋0⦌}
    {x'' y'' z'' : (U.diagram _⦋0⦌) _⦋0⦌}
    (hx : mappingVertexMap q x = x') (hy : mappingVertexMap q y = y')
    (hz : mappingVertexMap q z = z') (hx' : mappingVertexMap r x' = x'')
    (hy' : mappingVertexMap r y' = y'') (hz' : mappingVertexMap r z' = z'') :
    AdjacentTriangle.triangleMap q hx hy hz ≫ AdjacentTriangle.triangleMap r hx' hy' hz' =
      AdjacentTriangle.triangleMap (q ≫ r)
        ((congrArg (mappingVertexMap r) hx).trans hx')
        ((congrArg (mappingVertexMap r) hy).trans hy')
        ((congrArg (mappingVertexMap r) hz).trans hz') := by
  apply pullback.hom_ext
  · change (AdjacentTriangle.triangleMap q hx hy hz ≫
      AdjacentTriangle.triangleMap r hx' hy' hz') ≫ triangleProjection U x'' y'' z'' = _
    simp only [Category.assoc, AdjacentTriangle.triangleMap_projection,
      AdjacentTriangle.triangleMap_projection_assoc]
    rfl
  · change (AdjacentTriangle.triangleMap q hx hy hz ≫
      AdjacentTriangle.triangleMap r hx' hy' hz') ≫ triangleComparison U x'' y'' z'' = _
    simp only [Category.assoc, AdjacentTriangle.triangleMap_edges,
      AdjacentTriangle.triangleMap_edges_assoc]
    apply prod.hom_ext
    · simp only [Category.assoc, prod.map_fst, prod.map_fst_assoc]
      rw [mappingFibre.map_comp]
    · simp only [Category.assoc, prod.map_snd, prod.map_snd_assoc]
      rw [mappingFibre.map_comp]

/-- The original fixed-first triangle transport preserves identity maps. -/
@[simp]
theorem rightFixedMap_id (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (f : (mappingFibre W x y) _⦋0⦌) :
    rightFixedMap (𝟙 W) (x := x) (y := y) (x' := x) (y' := y)
      (f := f) (f' := f) rfl rfl (by simp) = 𝟙 _ := by
  apply pullback.hom_ext
  · simpa only [FixedEdgeTriangle.rightTriangleProjection, triangle_transport_id,
      Category.comp_id, Category.id_comp] using
      (rightFixedMap_triangle (𝟙 W) (x := x) (y := y) (x' := x) (y' := y)
        (f := f) (f' := f) rfl rfl (by simp))
  · simpa only [FixedEdgeTriangle.rightProjection, mappingFibre.map_id,
      Category.comp_id, Category.id_comp] using
      (rightFixedMap_candidate (𝟙 W) (x := x) (y := y) (x' := x) (y' := y)
        (f := f) (f' := f) rfl rfl (by simp))

/-- The original fixed-last triangle transport preserves identity maps. -/
@[simp]
theorem leftFixedMap_id (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (f : (mappingFibre W x y) _⦋0⦌) :
    leftFixedMap (𝟙 W) (x := x) (y := y) (x' := x) (y' := y)
      (f := f) (f' := f) rfl rfl (by simp) = 𝟙 _ := by
  apply pullback.hom_ext
  · simpa only [FixedEdgeTriangle.leftTriangleProjection, triangle_transport_id,
      Category.comp_id, Category.id_comp] using
      (leftFixedMap_triangle (𝟙 W) (x := x) (y := y) (x' := x) (y' := y)
        (f := f) (f' := f) rfl rfl (by simp))
  · simpa only [FixedEdgeTriangle.leftProjection, mappingFibre.map_id,
      Category.comp_id, Category.id_comp] using
      (leftFixedMap_candidate (𝟙 W) (x := x) (y := y) (x' := x) (y' := y)
        (f := f) (f' := f) rfl rfl (by simp))

/-- The right strict-space transport is the literal identity at an identity target map. -/
@[simp]
theorem rightMap_id (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (f : (mappingFibre W x y) _⦋0⦌) :
    rightMap (𝟙 W) (x := x) (y := y) (x' := x) (y' := y)
      (f := f) (f' := f) rfl rfl (by simp) = 𝟙 _ := by
  apply pullback.hom_ext
  · simpa only [rightFixedMap_id, Category.comp_id, Category.id_comp] using
      (rightMap_fixed (𝟙 W) (x := x) (y := y) (x' := x) (y' := y)
        (f := f) (f' := f) rfl rfl (by simp))
  · simpa only [Category.id_comp] using
      (rightMap_point (𝟙 W) (x := x) (y := y) (x' := x) (y' := y)
        (f := f) (f' := f) rfl rfl (by simp))

/-- The left strict-space transport is the literal identity at an identity target map. -/
@[simp]
theorem leftMap_id (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (f : (mappingFibre W x y) _⦋0⦌) :
    leftMap (𝟙 W) (x := x) (y := y) (x' := x) (y' := y)
      (f := f) (f' := f) rfl rfl (by simp) = 𝟙 _ := by
  apply pullback.hom_ext
  · simpa only [leftFixedMap_id, Category.comp_id, Category.id_comp] using
      (leftMap_fixed (𝟙 W) (x := x) (y := y) (x' := x) (y' := y)
        (f := f) (f' := f) rfl rfl (by simp))
  · simpa only [Category.id_comp] using
      (leftMap_point (𝟙 W) (x := x) (y := y) (x' := x) (y' := y)
        (f := f) (f' := f) rfl rfl (by simp))

/-- The paired transport is the literal identity on the same ordered product. -/
@[simp]
theorem pairedMap_id (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (f : (mappingFibre W x y) _⦋0⦌) :
    pairedMap (𝟙 W) (x := x) (y := y) (x' := x) (y' := y)
      (f := f) (f' := f) rfl rfl (by simp) = 𝟙 _ := by
  apply prod.hom_ext
  · rw [pairedMap_left, leftMap_id, Category.comp_id, Category.id_comp]
  · rw [pairedMap_right, rightMap_id, Category.comp_id, Category.id_comp]

variable {W V U : SimplicialSpace.{u}} (q : W ⟶ V) (r : V ⟶ U)
  {x y : (W.diagram _⦋0⦌) _⦋0⦌} {x' y' : (V.diagram _⦋0⦌) _⦋0⦌}
  {x'' y'' : (U.diagram _⦋0⦌) _⦋0⦌}
  {f : (mappingFibre W x y) _⦋0⦌} {f' : (mappingFibre V x' y') _⦋0⦌}
  {f'' : (mappingFibre U x'' y'') _⦋0⦌}
  (hx : mappingVertexMap q x = x') (hy : mappingVertexMap q y = y')
  (hx' : mappingVertexMap r x' = x'') (hy' : mappingVertexMap r y' = y'')
  (hf : (mappingFibre.map q hx hy).app (op ⦋0⦌) f = f')
  (hf' : (mappingFibre.map r hx' hy').app (op ⦋0⦌) f' = f'')

include hf hf' in
/-- The same original fixed arrow moves by the literal composite fibre map. -/
theorem edgeImage_comp :
    (mappingFibre.map (q ≫ r) ((congrArg (mappingVertexMap r) hx).trans hx')
      ((congrArg (mappingVertexMap r) hy).trans hy')).app (op ⦋0⦌) f = f'' := by
  rw [← mappingFibre.map_comp q r hx hy hx' hy']
  change (mappingFibre.map r hx' hy').app (op ⦋0⦌)
    ((mappingFibre.map q hx hy).app (op ⦋0⦌) f) = f''
  rw [hf, hf']

/-- The actual fixed-first transport preserves original target-map composition. -/
theorem rightFixedMap_comp :
    rightFixedMap q hx hy hf ≫ rightFixedMap r hx' hy' hf' =
      rightFixedMap (q ≫ r) ((congrArg (mappingVertexMap r) hx).trans hx')
        ((congrArg (mappingVertexMap r) hy).trans hy')
        (edgeImage_comp q r hx hy hx' hy' hf hf') := by
  apply pullback.hom_ext
  · change (rightFixedMap q hx hy hf ≫ rightFixedMap r hx' hy' hf') ≫
      FixedEdgeTriangle.rightTriangleProjection U x'' y'' f'' =
        rightFixedMap (q ≫ r) ((congrArg (mappingVertexMap r) hx).trans hx')
          ((congrArg (mappingVertexMap r) hy).trans hy')
          (edgeImage_comp q r hx hy hx' hy' hf hf') ≫
            FixedEdgeTriangle.rightTriangleProjection U x'' y'' f''
    simp only [Category.assoc, rightFixedMap_triangle, rightFixedMap_triangle_assoc]
    rw [triangle_transport_comp]
  · change (rightFixedMap q hx hy hf ≫ rightFixedMap r hx' hy' hf') ≫
      FixedEdgeTriangle.rightProjection U x'' y'' f'' =
        rightFixedMap (q ≫ r) ((congrArg (mappingVertexMap r) hx).trans hx')
          ((congrArg (mappingVertexMap r) hy).trans hy')
          (edgeImage_comp q r hx hy hx' hy' hf hf') ≫
            FixedEdgeTriangle.rightProjection U x'' y'' f''
    simp only [Category.assoc, rightFixedMap_candidate, rightFixedMap_candidate_assoc]
    rw [mappingFibre.map_comp]

/-- The actual fixed-last transport preserves original target-map composition. -/
theorem leftFixedMap_comp :
    leftFixedMap q hx hy hf ≫ leftFixedMap r hx' hy' hf' =
      leftFixedMap (q ≫ r) ((congrArg (mappingVertexMap r) hx).trans hx')
        ((congrArg (mappingVertexMap r) hy).trans hy')
        (edgeImage_comp q r hx hy hx' hy' hf hf') := by
  apply pullback.hom_ext
  · change (leftFixedMap q hx hy hf ≫ leftFixedMap r hx' hy' hf') ≫
      FixedEdgeTriangle.leftTriangleProjection U x'' y'' f'' =
        leftFixedMap (q ≫ r) ((congrArg (mappingVertexMap r) hx).trans hx')
          ((congrArg (mappingVertexMap r) hy).trans hy')
          (edgeImage_comp q r hx hy hx' hy' hf hf') ≫
            FixedEdgeTriangle.leftTriangleProjection U x'' y'' f''
    simp only [Category.assoc, leftFixedMap_triangle, leftFixedMap_triangle_assoc]
    rw [triangle_transport_comp]
  · change (leftFixedMap q hx hy hf ≫ leftFixedMap r hx' hy' hf') ≫
      FixedEdgeTriangle.leftProjection U x'' y'' f'' =
        leftFixedMap (q ≫ r) ((congrArg (mappingVertexMap r) hx).trans hx')
          ((congrArg (mappingVertexMap r) hy).trans hy')
          (edgeImage_comp q r hx hy hx' hy' hf hf') ≫
            FixedEdgeTriangle.leftProjection U x'' y'' f''
    simp only [Category.assoc, leftFixedMap_candidate, leftFixedMap_candidate_assoc]
    rw [mappingFibre.map_comp]

/-- The right strict-space maps compose on the original vertices and the same moved f. -/
theorem rightMap_comp : rightMap q hx hy hf ≫ rightMap r hx' hy' hf' =
    rightMap (q ≫ r) ((congrArg (mappingVertexMap r) hx).trans hx')
      ((congrArg (mappingVertexMap r) hy).trans hy')
      (edgeImage_comp q r hx hy hx' hy' hf hf') := by
  apply pullback.hom_ext
  · change (rightMap q hx hy hf ≫ rightMap r hx' hy' hf') ≫ rightToFixed U x'' y'' f'' = _
    simp only [Category.assoc, rightMap_fixed, rightMap_fixed_assoc]
    rw [rightFixedMap_comp]
  · change (rightMap q hx hy hf ≫ rightMap r hx' hy' hf') ≫ rightToPoint U x'' y'' f'' = _
    simp only [Category.assoc, rightMap_point]

/-- The left strict-space maps compose on those same original vertices and fixed f. -/
theorem leftMap_comp : leftMap q hx hy hf ≫ leftMap r hx' hy' hf' =
    leftMap (q ≫ r) ((congrArg (mappingVertexMap r) hx).trans hx')
      ((congrArg (mappingVertexMap r) hy).trans hy')
      (edgeImage_comp q r hx hy hx' hy' hf hf') := by
  apply pullback.hom_ext
  · change (leftMap q hx hy hf ≫ leftMap r hx' hy' hf') ≫ leftToFixed U x'' y'' f'' = _
    simp only [Category.assoc, leftMap_fixed, leftMap_fixed_assoc]
    rw [leftFixedMap_comp]
  · change (leftMap q hx hy hf ≫ leftMap r hx' hy' hf') ≫ leftToPoint U x'' y'' f'' = _
    simp only [Category.assoc, leftMap_point]

/-- The literal paired maps preserve composition independently on b and c. -/
theorem pairedMap_comp : pairedMap q hx hy hf ≫ pairedMap r hx' hy' hf' =
    pairedMap (q ≫ r) ((congrArg (mappingVertexMap r) hx).trans hx')
      ((congrArg (mappingVertexMap r) hy).trans hy')
      (edgeImage_comp q r hx hy hx' hy' hf hf') := by
  apply prod.hom_ext
  · simp only [Category.assoc, pairedMap_left, pairedMap_left_assoc]
    rw [leftMap_comp]
  · simp only [Category.assoc, pairedMap_right, pairedMap_right_assoc]
    rw [rightMap_comp]

end Functoriality

section Operators
variable {W V : SimplicialSpace.{u}} (q : W ⟶ V)
  {x y : (W.diagram _⦋0⦌) _⦋0⦌} {x' y' : (V.diagram _⦋0⦌) _⦋0⦌}
  {f : (mappingFibre W x y) _⦋0⦌} {f' : (mappingFibre V x' y') _⦋0⦌}
  (hx : mappingVertexMap q x = x') (hy : mappingVertexMap q y = y')
  (hf : (mappingFibre.map q hx hy).app (op ⦋0⦌) f = f')

/-- The original right strict-space map preserves every simplex operator in every degree. -/
theorem rightMap_operator {a b : SimplexCategoryᵒᵖ} (α : a ⟶ b) :
    (rightSpace W x y f).map α ≫ (rightMap q hx hy hf).app b =
      (rightMap q hx hy hf).app a ≫ (rightSpace V x' y' f').map α :=
  (rightMap q hx hy hf).naturality α

/-- The original left strict-space map preserves every simplex operator in every degree. -/
theorem leftMap_operator {a b : SimplexCategoryᵒᵖ} (α : a ⟶ b) :
    (leftSpace W x y f).map α ≫ (leftMap q hx hy hf).app b =
      (leftMap q hx hy hf).app a ≫ (leftSpace V x' y' f').map α :=
  (leftMap q hx hy hf).naturality α

/-- The original paired map preserves every simplex operator with both candidates independent. -/
theorem pairedMap_operator {a b : SimplexCategoryᵒᵖ} (α : a ⟶ b) :
    (pairedSpace W x y f).map α ≫ (pairedMap q hx hy hf).app b =
      (pairedMap q hx hy hf).app a ≫ (pairedSpace V x' y' f').map α :=
  (pairedMap q hx hy hf).naturality α

end Operators

end SimplicialSpace.InverseTriangle
