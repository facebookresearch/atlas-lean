/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.CellAnnulusQuotient
public import MathlibExt.CategoryTheory.SingleObj.Descent

/-!
# Actual weights on the original annular overlap

Normalize the constructed connector in each original square-annulus component
and use the derived annihilation of its End group to obtain the difference
formula there. Decode every point of the actual collar overlap through the
constructed overlap and sigma homeomorphisms. Index constancy of every actual
path class and the constructed full faithfulness of the component inclusion
then transport the component formula to every overlap arrow.

The resulting weight is total on the full subgroup-indexed overlap.
No global connector between distinct components, killed-loop premise, weight,
difference formula, object adjustment, van Kampen factorization or quotient
isomorphism is supplied as input.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology Topology.CWComplex

universe u

namespace AlgebraicTopology.CellAnnulusWeights

variable (X : TopCat.{u}) (x : X)
variable (P : Subgroup (FundamentalGroup X x)) [P.Normal]

/-- The constructed annular connector, normalized to be the identity at the
original square-annulus basepoint. -/
def normalizedConnector (z : classicalCellSquareAnnulus.{u}) :
    FundamentalGroupoid.mk classicalCellSquareAnnulusBasepoint.{u} ⟶
      FundamentalGroupoid.mk z :=
  inv (Path.Homotopic.Quotient.mk
      (classicalCellSquareAnnulusConnector classicalCellSquareAnnulusBasepoint.{u})) ≫
    Path.Homotopic.Quotient.mk (classicalCellSquareAnnulusConnector z)

/-- The normalized connector at the original basepoint is exactly the identity arrow. -/
theorem normalizedConnector_basepoint :
    normalizedConnector classicalCellSquareAnnulusBasepoint.{u} =
      𝟙 (FundamentalGroupoid.mk classicalCellSquareAnnulusBasepoint.{u}) := by
  simp [normalizedConnector]

/-- Restrict the actual annular quotient functor to one original raw component. -/
def componentFunctor (p : P) :
    FundamentalGroupoid classicalCellSquareAnnulus.{u} ⥤
      SingleObj (FundamentalGroup X x ⧸ P) :=
  FundamentalGroupoid.map (CellAnnulusCoordinates.componentInclusion 1 p) ⋙
    CellAnnulusQuotient.annulusQuotientFunctor X x P

/-- The actual component weight is the image of its normalized constructed connector. -/
def componentWeight (p : P) (z : classicalCellSquareAnnulus.{u}) :
    FundamentalGroup X x ⧸ P :=
  (componentFunctor X x P p).map (normalizedConnector z)

private theorem component_mapEnd_eq_one (p : P)
    (e : End (FundamentalGroupoid.mk classicalCellSquareAnnulusBasepoint.{u})) :
    (((componentFunctor X x P p).mapEnd
      (FundamentalGroupoid.mk classicalCellSquareAnnulusBasepoint.{u})) e).asHom =
        (1 : FundamentalGroup X x ⧸ P) := by
  change CellAnnulusQuotient.annulusQuotientEnd X x P p
      ((FundamentalGroupoid.map
        (CellAnnulusCoordinates.componentInclusion 1 p)).mapEnd
          (FundamentalGroupoid.mk classicalCellSquareAnnulusBasepoint.{u}) e) = 1
  exact CellAnnulusQuotient.mapEnd_eq_one X x P p _

/-- On each original raw component, every arrow has the derived difference formula. -/
theorem component_map_eq_difference (p : P)
    {c d : FundamentalGroupoid classicalCellSquareAnnulus.{u}} (f : c ⟶ d) :
    ((componentFunctor X x P p).map f : FundamentalGroup X x ⧸ P) =
      componentWeight X x P p d.as * (componentWeight X x P p c.as)⁻¹ := by
  simpa only [componentWeight] using
    CategoryTheory.SingleObj.map_eq_difference_of_kills_mapEnd
      (componentFunctor X x P p)
      (FundamentalGroupoid.mk classicalCellSquareAnnulusBasepoint.{u})
      (fun z : FundamentalGroupoid classicalCellSquareAnnulus.{u} =>
        normalizedConnector z.as)
      (component_mapEnd_eq_one X x P p) f

/-- The quotient-valued functor on the actual overlap, obtained from its original
left inclusion into the outer collar. -/
def overlapFunctor :
    FundamentalGroupoid
        ↥(CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P) ∩
          CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P)) ⥤
      SingleObj (FundamentalGroup X x ⧸ P) :=
  FundamentalGroupoid.map
      (MathlibExt.Topology.Homotopy.VanKampenWanted.inclusionInterLeft
        (CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P))
        (CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P))) ⋙
    CellQuotientFunctor.kappaU X x P 1 (LoopCellAttachment.attachingMap X x P)

/-- Decode the actual overlap through its original annulus and literal sigma
homeomorphisms. -/
def overlapSigmaHomeomorph :
    ↥(CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P) ∩
        CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P)) ≃ₜ
      (Σ _ : P, classicalCellSquareAnnulus.{u}) :=
  (CellAnnulusOverlap.homeomorph X 1 (LoopCellAttachment.attachingMap X x P)).symm.trans
    (CellAnnulusComponents.sigmaToFamilyHomeomorph P 1).symm

/-- The same actual decoded overlap point, retaining both its index and component point. -/
def overlapDecoded
    (z : ↥(CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P) ∩
      CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P))) :
    Σ _ : P, classicalCellSquareAnnulus.{u} :=
  overlapSigmaHomeomorph X x P z

/-- The original subgroup index of an actual overlap point. -/
def overlapIndex
    (z : ↥(CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P) ∩
      CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P))) : P :=
  (overlapDecoded X x P z).1

/-- The original square-annulus point decoded from an actual overlap point. -/
def overlapPoint
    (z : ↥(CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P) ∩
      CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P))) :
    classicalCellSquareAnnulus.{u} :=
  (overlapDecoded X x P z).2

omit [P.Normal] in
/-- The decoded index and point recover the original family-annulus point. -/
theorem componentInclusion_decoded
    (z : ↥(CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P) ∩
      CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P))) :
    CellAnnulusCoordinates.componentInclusion 1 (overlapIndex X x P z)
        (overlapPoint X x P z) =
      (CellAnnulusOverlap.homeomorph X 1
        (LoopCellAttachment.attachingMap X x P)).symm z := by
  let H := CellAnnulusOverlap.homeomorph X 1 (LoopCellAttachment.attachingMap X x P)
  let E := CellAnnulusComponents.sigmaToFamilyHomeomorph P 1
  let d := overlapDecoded X x P z
  change CellAnnulusCoordinates.componentInclusion 1 d.1 d.2 = H.symm z
  calc
    _ = E (Sigma.mk d.1 d.2) :=
      (CellAnnulusComponents.sigmaToFamilyHomeomorph_apply P 1 d.1 d.2).symm
    _ = E d := by cases d; rfl
    _ = H.symm z := by
      change E (E.symm (H.symm z)) = H.symm z
      exact E.apply_symm_apply (H.symm z)

omit [P.Normal] in
private theorem toOuter_comp_homeomorph_symm :
    (CellAnnulusDeformation.toOuter X 1 (LoopCellAttachment.attachingMap X x P)).comp
        (CellAnnulusOverlap.homeomorph X 1
          (LoopCellAttachment.attachingMap X x P)).symm.toHomotopyEquiv.toFun =
      MathlibExt.Topology.Homotopy.VanKampenWanted.inclusionInterLeft
        (CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P))
        (CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P)) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  exact (CellAnnulusDeformation.toOuter_val X 1
    (LoopCellAttachment.attachingMap X x P)
    ((CellAnnulusOverlap.homeomorph X 1
      (LoopCellAttachment.attachingMap X x P)).symm z)).trans
        (CellAnnulusOverlap.diskInclusion_homeomorph_symm X 1
          (LoopCellAttachment.attachingMap X x P) z)

private theorem overlapToAnnulus_comp_annulusQuotientFunctor :
    FundamentalGroupoid.map
        (CellAnnulusOverlap.homeomorph X 1
          (LoopCellAttachment.attachingMap X x P)).symm.toHomotopyEquiv.toFun ⋙
      CellAnnulusQuotient.annulusQuotientFunctor X x P =
        overlapFunctor X x P := by
  let A : Type u := CellCollarCover.annulus P 1
  let U : Type u := CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P)
  let O : Type u := ↥(CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P) ∩
    CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P))
  let h : C(O, A) :=
    (CellAnnulusOverlap.homeomorph X 1
      (LoopCellAttachment.attachingMap X x P)).symm.toHomotopyEquiv.toFun
  let s : C(A, U) :=
    CellAnnulusDeformation.toOuter X 1 (LoopCellAttachment.attachingMap X x P)
  let j : C(O, U) :=
    MathlibExt.Topology.Homotopy.VanKampenWanted.inclusionInterLeft
      (CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P))
      (CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P))
  let K : FundamentalGroupoid U ⥤ SingleObj (FundamentalGroup X x ⧸ P) :=
    CellQuotientFunctor.kappaU X x P 1 (LoopCellAttachment.attachingMap X x P)
  have hMap : s.comp h = j := toOuter_comp_homeomorph_symm X x P
  calc
    _ = (FundamentalGroupoid.map h ⋙ FundamentalGroupoid.map s) ⋙ K := rfl
    _ = FundamentalGroupoid.map (s.comp h) ⋙ K :=
      congrArg (fun F : FundamentalGroupoid O ⥤ FundamentalGroupoid U => F ⋙ K)
        (FundamentalGroupoid.map_comp s h).symm
    _ = FundamentalGroupoid.map j ⋙ K :=
      congrArg
        (fun f : C(O, U) => FundamentalGroupoid.map f ⋙ K) hMap
    _ = _ := rfl

/-- The total actual overlap weight, assembled independently in the component
decoded from each original overlap object. -/
def overlapWeight
    (z : FundamentalGroupoid
      ↥(CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P) ∩
        CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P))) :
    FundamentalGroup X x ⧸ P :=
  componentWeight X x P (overlapIndex X x P z.as) (overlapPoint X x P z.as)

/-- Every actual overlap arrow satisfies the derived difference formula for the
total componentwise weight. -/
theorem overlap_map_eq_difference
    {c d : FundamentalGroupoid
      ↥(CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P) ∩
        CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P))}
    (f : c ⟶ d) :
    ((overlapFunctor X x P).map f : FundamentalGroup X x ⧸ P) =
      overlapWeight X x P d * (overlapWeight X x P c)⁻¹ := by
  let O : Type u := ↥(CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P) ∩
    CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P))
  let A : Type u := CellCollarCover.annulus P 1
  let Q : Type u := FundamentalGroup X x ⧸ P
  let H := CellAnnulusOverlap.homeomorph X 1 (LoopCellAttachment.attachingMap X x P)
  let h : C(O, A) := H.symm.toHomotopyEquiv.toFun
  let F_A : FundamentalGroupoid A ⥤ SingleObj Q :=
    CellAnnulusQuotient.annulusQuotientFunctor X x P
  let F_O : FundamentalGroupoid O ⥤ SingleObj Q := overlapFunctor X x P
  rcases hC : overlapDecoded X x P c.as with ⟨p, a⟩
  rcases hD : overlapDecoded X x P d.as with ⟨p', a'⟩
  have hIndex := FundamentalGroupoid.SigmaComponent.hom_index_eq
    (fun _ : P => classicalCellSquareAnnulus.{u})
    ((FundamentalGroupoid.map
      (overlapSigmaHomeomorph X x P).toHomotopyEquiv.toFun).map f)
  change (overlapDecoded X x P c.as).1 = (overlapDecoded X x P d.as).1 at hIndex
  rw [hC, hD] at hIndex
  change p = p' at hIndex
  subst p'
  let j : C(classicalCellSquareAnnulus.{u}, A) :=
    CellAnnulusCoordinates.componentInclusion 1 p
  have hCPoint : j a = h c.as := by
    change j a = H.symm c.as
    simpa only [j, overlapIndex, overlapPoint, hC] using
      componentInclusion_decoded X x P c.as
  have hDPoint : j a' = h d.as := by
    change j a' = H.symm d.as
    simpa only [j, overlapIndex, overlapPoint, hD] using
      componentInclusion_decoded X x P d.as
  have hCObj :
      (FundamentalGroupoid.map j).obj (FundamentalGroupoid.mk a) =
        (FundamentalGroupoid.map h).obj c :=
    congrArg FundamentalGroupoid.mk hCPoint
  have hDObj :
      (FundamentalGroupoid.map j).obj (FundamentalGroupoid.mk a') =
        (FundamentalGroupoid.map h).obj d :=
    congrArg FundamentalGroupoid.mk hDPoint
  let qA : (FundamentalGroupoid.map h).obj c ⟶
      (FundamentalGroupoid.map h).obj d :=
    (FundamentalGroupoid.map h).map f
  let qFamily :
      (FundamentalGroupoid.map j).obj (FundamentalGroupoid.mk a) ⟶
        (FundamentalGroupoid.map j).obj (FundamentalGroupoid.mk a') :=
    (eqToHom hCObj ≫ qA) ≫ eqToHom hDObj.symm
  let qComponent : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk a' :=
    (CellAnnulusComponents.componentFullyFaithful P 1 p).preimage qFamily
  have hPreimage :
      (FundamentalGroupoid.map j).map qComponent = qFamily :=
    CellAnnulusComponents.componentFullyFaithful_map_preimage P 1 p qFamily
  have hSourceEq :
      F_A.map (eqToHom hCObj) = 𝟙 _ := by
    rw [eqToHom_map, eqToHom_refl]
  have hTargetEq :
      F_A.map (eqToHom hDObj.symm) = 𝟙 _ := by
    rw [eqToHom_map, eqToHom_refl]
  have hFamilyValue : F_A.map qFamily = F_A.map qA := by
    dsimp only [qFamily]
    rw [Functor.map_comp, Functor.map_comp, hSourceEq, hTargetEq,
      Category.id_comp, Category.comp_id]
  have hComponentValue :
      ((componentFunctor X x P p).map qComponent : Q) = (F_A.map qFamily : Q) := by
    change (F_A.map ((FundamentalGroupoid.map j).map qComponent) : Q) = F_A.map qFamily
    rw [hPreimage]
  have hPullback := congrArg
    (fun F : FundamentalGroupoid O ⥤ SingleObj Q => (F.map f : Q))
    (overlapToAnnulus_comp_annulusQuotientFunctor X x P)
  change (F_A.map qA : Q) = (F_O.map f : Q) at hPullback
  have hValue :
      ((componentFunctor X x P p).map qComponent : Q) = (F_O.map f : Q) :=
    hComponentValue.trans (hFamilyValue.trans hPullback)
  have hFormula :
      ((componentFunctor X x P p).map qComponent : Q) =
        componentWeight X x P p a' * (componentWeight X x P p a)⁻¹ := by
    exact component_map_eq_difference X x P p qComponent
  calc
    (F_O.map f : Q) = (componentFunctor X x P p).map qComponent := hValue.symm
    _ = componentWeight X x P p a' * (componentWeight X x P p a)⁻¹ := hFormula
    _ = overlapWeight X x P d * (overlapWeight X x P c)⁻¹ := by
      simp only [overlapWeight, overlapIndex, overlapPoint, hC, hD]

end AlgebraicTopology.CellAnnulusWeights

end

end
