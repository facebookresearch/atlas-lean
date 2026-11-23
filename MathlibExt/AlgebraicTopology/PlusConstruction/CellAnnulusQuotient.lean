/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.CellQuotientFunctor
public import MathlibExt.AlgebraicTopology.PlusConstruction.CellAnnulusOverlap
public import MathlibExt.AlgebraicTopology.PlusConstruction.AnnulusLoopTransport

/-!
# The original quotient kills the actual annulus components

Restrict the constructed quotient-valued functor on the outer collar along
the original annular characteristic map. The transported outer perimeter is
killed because its retraction is the same original subgroup element. Actual
path conjugation then kills the untransported outer perimeter, and the proved
annulus comparison kills the same component perimeter. Since that perimeter
generates every component End group by integer powers, every original
component End element is killed.

No killed-loop, connector, weight or factorization witness is an input here.
The construction retains the original basepoints, paths, equality casts, End
order and one-object-groupoid convention. It assumes neither connectedness nor
perfectness and constructs no global quotient or quotient isomorphism.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology Topology.CWComplex

universe u

namespace AlgebraicTopology.CellAnnulusQuotient

variable (X : TopCat.{u}) (x : X)
variable (P : Subgroup (FundamentalGroup X x)) [P.Normal]

/-- The actual quotient-valued functor on the original subgroup-indexed annulus. -/
def annulusQuotientFunctor :
    FundamentalGroupoid (CellCollarCover.annulus P 1) ⥤
      SingleObj (FundamentalGroup X x ⧸ P) :=
  FundamentalGroupoid.map
      (CellAnnulusDeformation.toOuter X 1 (LoopCellAttachment.attachingMap X x P)) ⋙
    CellQuotientFunctor.kappaU X x P 1 (LoopCellAttachment.attachingMap X x P)

/-- The actual component End homomorphism of the annular quotient functor. -/
def annulusQuotientEnd (p : P) :
    FundamentalGroup (CellCollarCover.annulus P 1)
        (CellAnnulusComponents.basepoint P p) →*
      (FundamentalGroup X x ⧸ P) :=
  (SingleObj.toEnd (FundamentalGroup X x ⧸ P)).symm.toMonoidHom.comp
    ((annulusQuotientFunctor X x P).mapEnd
      (FundamentalGroupoid.mk (CellAnnulusComponents.basepoint P p)))

/-- The quotient functor kills the same outer perimeter transported to the included
original basepoint. -/
theorem transportedOuterPerimeterClass_eq_one (p : P) :
    (SingleObj.toEnd (FundamentalGroup X x ⧸ P)).symm
      ((CellQuotientFunctor.kappaU X x P 1 (LoopCellAttachment.attachingMap X x P)).mapEnd
        (FundamentalGroupoid.mk
          (CellCollarDeformation.inclusionU X 1
            (LoopCellAttachment.attachingMap X x P) x))
        (LoopCellAttachment.transportedOuterPerimeterClass X x P p)) = 1 := by
  let U : Type u := CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P)
  let r : C(U, X) :=
    (CellCollarDeformation.retractionU X 1 (LoopCellAttachment.attachingMap X x P)).hom
  let b : U :=
    CellCollarDeformation.inclusionU X 1 (LoopCellAttachment.attachingMap X x P) x
  let F : FundamentalGroupoid U ⥤ SingleObj (FundamentalGroup X x ⧸ P) :=
    CellQuotientFunctor.kappaU X x P 1 (LoopCellAttachment.attachingMap X x P)
  let q : FundamentalGroup U b :=
    LoopCellAttachment.transportedOuterPerimeterClass X x P p
  have h := DFunLike.congr_fun
    (CellQuotientFunctor.kappaU_originalEnd X x P 1
      (LoopCellAttachment.attachingMap X x P)) q
  change (SingleObj.toEnd (FundamentalGroup X x ⧸ P)).symm
      (F.mapEnd (FundamentalGroupoid.mk b) q) =
    QuotientGroup.mk' P
      (FundamentalGroup.mapOfEq r
        (CellQuotientFunctor.retraction_includedBasepoint X x 1
          (LoopCellAttachment.attachingMap X x P)) q) at h
  have hRetraction :
      FundamentalGroup.mapOfEq r
          (CellQuotientFunctor.retraction_includedBasepoint X x 1
            (LoopCellAttachment.attachingMap X x P)) q = p.val := by
    exact LoopCellAttachment.retraction_transportedOuterPerimeterClass X x P p
  have hSubgroup := DFunLike.congr_fun (QuotientGroup.mk'_comp_subtype P) p
  change QuotientGroup.mk' P p.val = 1 at hSubgroup
  exact h.trans ((congrArg (QuotientGroup.mk' P) hRetraction).trans hSubgroup)

/-- Actual path conjugation and cancellation kill the original untransported outer perimeter. -/
theorem outerPerimeterClass_eq_one (p : P) :
    (SingleObj.toEnd (FundamentalGroup X x ⧸ P)).symm
      ((CellQuotientFunctor.kappaU X x P 1 (LoopCellAttachment.attachingMap X x P)).mapEnd
        (FundamentalGroupoid.mk (LoopCellAttachment.outerBasepoint X x P p))
        (LoopCellAttachment.outerPerimeterClass X x P p)) = 1 := by
  let U : Type u := CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P)
  let F : FundamentalGroupoid U ⥤ SingleObj (FundamentalGroup X x ⧸ P) :=
    CellQuotientFunctor.kappaU X x P 1 (LoopCellAttachment.attachingMap X x P)
  let b : U := LoopCellAttachment.outerBasepoint X x P p
  let b₀ : U :=
    CellCollarDeformation.inclusionU X 1 (LoopCellAttachment.attachingMap X x P) x
  let γ : Path b b₀ := LoopCellAttachment.outerBasepointPath X x P p
  let q : FundamentalGroup U b := LoopCellAttachment.outerPerimeterClass X x P p
  let q₀ : FundamentalGroup U b₀ :=
    LoopCellAttachment.transportedOuterPerimeterClass X x P p
  let τ : FundamentalGroupoid.mk b ≅ FundamentalGroupoid.mk b₀ :=
    (Groupoid.isoEquivHom _ _).symm (Path.Homotopic.Quotient.mk γ)
  have hTransport : F.mapEnd (FundamentalGroupoid.mk b₀) q₀ = 1 := by
    apply (SingleObj.toEnd (FundamentalGroup X x ⧸ P)).symm.injective
    simpa only [map_one] using transportedOuterPerimeterClass_eq_one X x P p
  have hTransportEq : q₀ = τ.conj q := rfl
  have hConjugated : F.mapEnd (FundamentalGroupoid.mk b₀) (τ.conj q) = 1 := by
    rw [← hTransportEq]
    exact hTransport
  have hMapConj :
      F.mapEnd (FundamentalGroupoid.mk b₀) (τ.conj q) =
        (F.mapIso τ).conj (F.mapEnd (FundamentalGroupoid.mk b) q) := by
    apply End.ext
    exact F.map_conj τ q
  have hConjugatedImage :
      (F.mapIso τ).conj (F.mapEnd (FundamentalGroupoid.mk b) q) = 1 :=
    hMapConj.symm.trans hConjugated
  have hOuter : F.mapEnd (FundamentalGroupoid.mk b) q = 1 := by
    apply (F.mapIso τ).conj.injective
    simpa only [map_one] using hConjugatedImage
  simpa only [map_one] using
    congrArg (SingleObj.toEnd (FundamentalGroup X x ⧸ P)).symm hOuter

/-- The actual annular quotient functor kills the same original family perimeter class. -/
theorem perimeterClass_eq_one (p : P) :
    annulusQuotientEnd X x P p (CellAnnulusComponents.perimeterClass P p) = 1 := by
  let A : Type u := CellCollarCover.annulus P 1
  let U : Type u := CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P)
  let s : C(A, U) :=
    CellAnnulusDeformation.toOuter X 1 (LoopCellAttachment.attachingMap X x P)
  let R : FundamentalGroupoid A ⥤ FundamentalGroupoid U := FundamentalGroupoid.map s
  let F : FundamentalGroupoid U ⥤ SingleObj (FundamentalGroup X x ⧸ P) :=
    CellQuotientFunctor.kappaU X x P 1 (LoopCellAttachment.attachingMap X x P)
  let bA : FundamentalGroupoid A :=
    FundamentalGroupoid.mk (CellAnnulusComponents.basepoint P p)
  let bU : FundamentalGroupoid U :=
    FundamentalGroupoid.mk (LoopCellAttachment.outerBasepoint X x P p)
  let gA : FundamentalGroup A (CellAnnulusComponents.basepoint P p) :=
    CellAnnulusComponents.perimeterClass P p
  let gU : FundamentalGroup U (LoopCellAttachment.outerBasepoint X x P p) :=
    LoopCellAttachment.outerPerimeterClass X x P p
  have hBasepoint : s (CellAnnulusComponents.basepoint P p) =
      LoopCellAttachment.outerBasepoint X x P p :=
    CellAnnulusOverlap.toOuter_basepoint X x P p
  let α : R.obj bA ≅ bU := eqToIso (congrArg FundamentalGroupoid.mk hBasepoint)
  have hClass := CellAnnulusOverlap.toOuter_perimeterClass X x P p
  change α.conj (R.mapEnd bA gA) = gU at hClass
  have hOuter : F.mapEnd bU gU = 1 := by
    apply (SingleObj.toEnd (FundamentalGroup X x ⧸ P)).symm.injective
    simpa only [map_one] using outerPerimeterClass_eq_one X x P p
  have hMapConj :
      F.mapEnd bU (α.conj (R.mapEnd bA gA)) =
        (F.mapIso α).conj (F.mapEnd (R.obj bA) (R.mapEnd bA gA)) := by
    apply End.ext
    exact F.map_conj α (R.mapEnd bA gA)
  have hConjugatedImage :
      (F.mapIso α).conj (F.mapEnd (R.obj bA) (R.mapEnd bA gA)) = 1 := by
    calc
      _ = F.mapEnd bU (α.conj (R.mapEnd bA gA)) := hMapConj.symm
      _ = F.mapEnd bU gU := congrArg (F.mapEnd bU) hClass
      _ = 1 := hOuter
  have hComponent : F.mapEnd (R.obj bA) (R.mapEnd bA gA) = 1 := by
    apply (F.mapIso α).conj.injective
    simpa only [map_one] using hConjugatedImage
  change (SingleObj.toEnd (FundamentalGroup X x ⧸ P)).symm
      (F.mapEnd (R.obj bA) (R.mapEnd bA gA)) = 1
  simpa only [map_one] using
    congrArg (SingleObj.toEnd (FundamentalGroup X x ⧸ P)).symm hComponent

/-- Every original End element in every actual indexed annulus component is killed. -/
theorem mapEnd_eq_one (p : P)
    (q : FundamentalGroup (CellCollarCover.annulus P 1)
      (CellAnnulusComponents.basepoint P p)) :
    annulusQuotientEnd X x P p q = 1 := by
  obtain ⟨n, hn⟩ := CellAnnulusComponents.exists_perimeter_zpow P p q
  calc
    annulusQuotientEnd X x P p q =
        annulusQuotientEnd X x P p (CellAnnulusComponents.perimeterClass P p ^ n) :=
      congrArg (annulusQuotientEnd X x P p) hn
    _ = annulusQuotientEnd X x P p (CellAnnulusComponents.perimeterClass P p) ^ n :=
      map_zpow (annulusQuotientEnd X x P p)
        (CellAnnulusComponents.perimeterClass P p) n
    _ = 1 ^ n := congrArg (fun z : FundamentalGroup X x ⧸ P => z ^ n)
      (perimeterClass_eq_one X x P p)
    _ = 1 := one_zpow n

end AlgebraicTopology.CellAnnulusQuotient

end

end
