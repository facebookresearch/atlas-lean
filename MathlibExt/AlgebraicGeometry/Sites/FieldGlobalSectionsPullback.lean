/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado

module

public import MathlibExt.AlgebraicGeometry.Sites.FieldInverseImageStalks
public import MathlibExt.AlgebraicGeometry.Sites.FieldGlobalSectionsInvariants
public import MathlibExt.AlgebraicGeometry.Sites.FieldContinuousCohomologyDerivedInvariants
public import MathlibExt.CategoryTheory.NatIso.ComparisonCoherence
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Field pullback on global sections and invariant normalization

Let k,Ω,K,Ψ be fields of universe u with Ω and Ψ prescribed separable closures of k and K. A
FieldMap e consists of embeddings σ : k → K and τ : Ω → Ψ with τ∘(k→Ω)=(K→Ψ)∘σ. Its spectrum
map f : Spec(K) → Spec(k) induces inverse image on small-étale sheaves.

The global-section map uses the inverse-image adjunction unit and the comparison between the
base-changed identity object and id_{Spec(K)}. Under Γ≅Galois invariants it is invariant
restriction along Gal(Ψ/K) → Gal(Ω/k), followed by the stalk-module comparison. These maps are
natural in sheaves, and coefficient groups of size w are lifted once to max(u,w).
-/

@[expose] public section

noncomputable section

set_option autoImplicit false


section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.DerivedSections

variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ] [IsSepClosure k Ω] [IsSepClosure K Ψ]
attribute [local instance] IsSepClosure.sep_closed

/-- Let e be compatible embeddings of field pairs (k,Ω) → (K,Ψ), with spectrum map f : Spec(K) →
Spec(k). The base change of the identity étale object over Spec(k) is canonically isomorphic
to the identity étale object over Spec(K). This is fieldBaseChangeTerminalIso(e). -/
def fieldBaseChangeTerminalIso (e : GaloisUnits.FieldMap k Ω K Ψ) :
    (smallEtaleBaseChange (fieldOriginalPullback k Ω K Ψ e)).obj (fieldIdentityEtale k) ≅
      fieldIdentityEtale K := by
  letI := smallEtaleBaseChange_preservesFiniteLimits (fieldOriginalPullback k Ω K Ψ e)
  exact ((identityEtaleIsTerminal (Spec (.of k))).isTerminalObj
    (smallEtaleBaseChange (fieldOriginalPullback k Ω K Ψ e)) (fieldIdentityEtale k)).uniqueUpToIso
      (identityEtaleIsTerminal (Spec (.of K)))

/-- For compatible field embeddings e and f : Spec(K) → Spec(k), define Γ_k(Q) → Γ_K(f^*Q) on
small-étale additive-group sheaves of height max(u,w). Normalize a section at id_{Spec(k)},
apply Q → f_*f^*Q, restrict along the inverse terminal-object base-change comparison, and
return to global sections over K. -/
def fieldPullbackGlobalSections (e : GaloisUnits.FieldMap k Ω K Ψ) :
    Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} ⟶
      smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
        Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w} := by
  let f := fieldOriginalPullback k Ω K Ψ e
  let L := smallEtaleInverseImage.{u, w} f
  let EY := (sheafSections (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).obj
    (op (fieldIdentityEtale k))
  let EB := (sheafSections (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).obj
    (op ((smallEtaleBaseChange f).obj (fieldIdentityEtale k)))
  let EX := (sheafSections (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).obj
    (op (fieldIdentityEtale K))
  let η : EY ⟶ L ⋙ EB :=
    Functor.whiskerRight (smallEtaleInverseImageAdjunction.{u, w} f).unit EY
  let r : EB ⟶ EX :=
    (sheafSections (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).map
      (fieldBaseChangeTerminalIso k Ω K Ψ e).inv.op
  exact (fieldGammaSectionsIso.{u, w} k).hom ≫ η ≫
    Functor.whiskerLeft L r ≫ Functor.whiskerLeft L (fieldGammaSectionsIso.{u, w} K).inv

omit [IsSepClosure k Ω] [IsSepClosure K Ψ] in
set_option backward.isDefEq.respectTransparency false in
-- V2/V3 implicit simplification could not see the same terminal-evaluation aliases.
theorem fieldPullbackGlobalSections_terminal_section
    (e : GaloisUnits.FieldMap k Ω K Ψ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldPullbackGlobalSections.{u, w} k Ω K Ψ e).app Q ≫
        (fieldGammaSectionsIso.{u, w} K).hom.app
          ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q) =
      (fieldGammaSectionsIso.{u, w} k).hom.app Q ≫
        ((smallEtaleInverseImageAdjunction.{u, w}
          (fieldOriginalPullback k Ω K Ψ e)).unit.app Q).hom.app (op (fieldIdentityEtale k)) ≫
        (((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q).obj.map
          (fieldBaseChangeTerminalIso k Ω K Ψ e).inv.op) := by
  change ((fieldGammaSectionsIso.{u, w} k).hom.app Q ≫
      ((smallEtaleInverseImageAdjunction.{u, w}
        (fieldOriginalPullback k Ω K Ψ e)).unit.app Q).hom.app (op (fieldIdentityEtale k)) ≫
      (((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q).obj.map
        (fieldBaseChangeTerminalIso k Ω K Ψ e).inv.op) ≫
      (fieldGammaSectionsIso.{u, w} K).inv.app
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)) ≫ _ = _
  exact CategoryTheory.comp_three_iso_inv_hom
    ((fieldGammaSectionsIso.{u, w} k).hom.app Q)
    (((smallEtaleInverseImageAdjunction.{u, w}
      (fieldOriginalPullback k Ω K Ψ e)).unit.app Q).hom.app (op (fieldIdentityEtale k)))
    (((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q).obj.map
      (fieldBaseChangeTerminalIso k Ω K Ψ e).inv.op)
    ((fieldGammaSectionsIso.{u, w} K).app
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q))


/-- Let e : (k,Ω) → (K,Ψ) be compatible embeddings of fields with prescribed separable closures.
The inverse isomorphism id_{Spec(K)} → f^*(id_{Spec(k)}) sends the terminal geometric point
from Ψ to fieldChangeOriginalPoint(e,id_k,z_k). Thus the terminal point agrees with the
specified point change. -/
theorem fieldBaseChangeTerminalPoint (e : GaloisUnits.FieldMap k Ω K Ψ) :
    (fieldGeometricPoint K Ψ).fiber.map (fieldBaseChangeTerminalIso k Ω K Ψ e).inv
        (fieldTerminalFiberPoint K Ψ) =
      fieldChangeOriginalPoint k Ω K Ψ e (fieldIdentityEtale k) (fieldTerminalFiberPoint k Ω) := by
  let F := (fieldGeometricPoint K Ψ).fiber
  let i := fieldBaseChangeTerminalIso k Ω K Ψ e
  let t := fieldChangeOriginalPoint k Ω K Ψ e (fieldIdentityEtale k) (fieldTerminalFiberPoint k Ω)
  have ht : F.map i.hom t = fieldTerminalFiberPoint K Ψ := Subsingleton.elim _ _
  exact F.map_iso_inv_point i t (fieldTerminalFiberPoint K Ψ) ht

theorem fieldBaseChangeTerminalCommonPoint (e : GaloisUnits.FieldMap k Ω K Ψ) :
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap K Ψ)).fiber.map
        (fieldBaseChangeTerminalIso k Ω K Ψ e).inv (ULift.up (fieldTerminalFiberPoint K Ψ)) =
      ULift.up (fieldChangeOriginalPoint k Ω K Ψ e (fieldIdentityEtale k)
        (fieldTerminalFiberPoint k Ω)) :=
  congrArg ULift.up (fieldBaseChangeTerminalPoint k Ω K Ψ e)

set_option backward.isDefEq.respectTransparency false in
-- V6 recorded a Trans-synthesis failure at the same sheaf/presheaf stalk aliases.
/-- For compatible field embeddings with prescribed closures, let c∈Γ_k(Q), let a be its value
under Γ_k(Q)≅Φ_k(Q)^G, and let ξ_e be the underlying stalk comparison. The invariant vector
associated to the pullback section in Γ_K(f^*Q) has underlying value ξ_e(a). The coefficient
universe is max(u,w). -/
theorem fieldPullbackGlobalSections_invariant_val (e : GaloisUnits.FieldMap k Ω K Ψ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (c : (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).obj Q) :
    ((fieldGlobalSectionsInvariantsIso.{u, w} K Ψ).hom.app
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)
          ((fieldPullbackGlobalSections.{u, w} k Ω K Ψ e).app Q c)).val =
      (fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q
        (((fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app Q c).val) := by
  let f := fieldOriginalPullback k Ω K Ψ e
  let F := (smallEtaleInverseImage.{u, w} f).obj Q
  let Φ := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap K Ψ)
  let U := fieldIdentityEtale k
  let V := fieldIdentityEtale K
  let z := fieldTerminalFiberPoint k Ω
  let y := fieldTerminalFiberPoint K Ψ
  let t := fieldChangeOriginalPoint k Ω K Ψ e U z
  let i := fieldBaseChangeTerminalIso k Ω K Ψ e
  let a := (fieldGammaSectionsIso.{u, w} k).hom.app Q c
  let d := ((smallEtaleInverseImageAdjunction.{u, w} f).unit.app Q).hom.app (op U) a
  have hs := fieldGlobalSectionsInvariantsIso_germ.{u, w} k Ω Q c
  have ht := fieldGlobalSectionsInvariantsIso_germ.{u, w} K Ψ F
    ((fieldPullbackGlobalSections.{u, w} k Ω K Ψ e).app Q c)
  have hsec := ConcreteCategory.congr_hom
    (fieldPullbackGlobalSections_terminal_section.{u, w} k Ω K Ψ e Q) c
  have hw := Φ.toPresheafFiber_w_apply i.inv (ULift.up y) F.obj d
  have hp := fieldBaseChangeTerminalCommonPoint.{u, w} k Ω K Ψ e
  have hg := fieldChangeUnderlyingStalkIso_original_germ_apply.{u, w} k Ω K Ψ e Q U z a
  have h1 : Φ.toPresheafFiber V (ULift.up y) F.obj
      ((fieldGammaSectionsIso.{u, w} K).hom.app F
        ((fieldPullbackGlobalSections.{u, w} k Ω K Ψ e).app Q c)) =
      Φ.toPresheafFiber V (ULift.up y) F.obj (F.obj.map i.inv.op d) :=
    congrArg (fun v => Φ.toPresheafFiber V (ULift.up y) F.obj v) hsec
  have h2 : Φ.toPresheafFiber V (ULift.up y) F.obj (F.obj.map i.inv.op d) =
      Φ.toPresheafFiber ((smallEtaleBaseChange f).obj U)
        (Φ.fiber.map i.inv (ULift.up y)) F.obj d := hw
  have h3 : Φ.toPresheafFiber ((smallEtaleBaseChange f).obj U)
      (Φ.fiber.map i.inv (ULift.up y)) F.obj d =
      Φ.toPresheafFiber ((smallEtaleBaseChange f).obj U) (ULift.up t) F.obj d :=
    congrArg (fun p => Φ.toPresheafFiber ((smallEtaleBaseChange f).obj U) p F.obj d) hp
  have h4 := congrArg
    (fun v => (fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q v) hs.symm
  exact ht.trans (h1.trans (h2.trans (h3.trans (hg.symm.trans h4))))

/-- Let e be a compatible map of fields with prescribed closures, χ : Gal(Ψ/K) → Gal(Ω/k) its
continuous restriction, and ξ_e : Res_χ Φ_k(Q) ≅ Φ_K(f^*Q) the stalk-module comparison. Under
the two Γ/invariant isomorphisms, a section c pulls back to Inv(ξ_e)(ResInv_χ(e_k(c))). This
equality is of invariant-subgroup elements. -/
theorem fieldPullbackGlobalSections_invariants (e : GaloisUnits.FieldMap k Ω K Ψ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (c : (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).obj Q) :
    (fieldGlobalSectionsInvariantsIso.{u, w} K Ψ).hom.app
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)
          ((fieldPullbackGlobalSections.{u, w} k Ω K Ψ e).app Q c) =
      DiscreteAbelianAction.invariantsFunctor.map
        ((fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app Q)
        ((fieldInvariantRestriction.{u, u, w} k Ω K Ψ
          (GaloisUnits.FieldMap.restrictContinuous e)).app
            ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)
              ((fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app Q c)) := by
  apply Subtype.ext
  exact fieldPullbackGlobalSections_invariant_val.{u, w} k Ω K Ψ e Q c


/-- For compatible field embeddings with prescribed closures, let γ : Γ_k → f^*⋙Γ_K, e_k,e_K the
Γ/invariant isomorphisms, χ the Galois restriction, and ξ_e the changed-stalk module
isomorphism. Then γ followed by e_K equals e_k followed by invariant restriction along χ and
invariants of ξ_e, as natural transformations on small-étale sheaves. -/
theorem fieldPullbackGlobalSections_invariants_naturality
    (e : GaloisUnits.FieldMap k Ω K Ψ) :
    fieldPullbackGlobalSections.{u, w} k Ω K Ψ e ≫
        Functor.whiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
          (fieldGlobalSectionsInvariantsIso.{u, w} K Ψ).hom =
      (fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom ≫
        Functor.whiskerLeft (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
          (fieldInvariantRestriction.{u, u, w} k Ω K Ψ
            (GaloisUnits.FieldMap.restrictContinuous e)) ≫
        Functor.whiskerRight (fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom
          (fieldInvariantFunctor.{u, w} K Ψ) := by
  apply NatTrans.ext
  funext Q
  ext c
  exact fieldPullbackGlobalSections_invariants.{u, w} k Ω K Ψ e Q c

/-- Let e be compatible embeddings of prescribed field closures, F a small-étale sheaf of
coefficient size w, and Q=ULift^u(F). For c∈F(U) and a geometric lift z to U, the underlying
stalk comparison sends the germ of up(c) at up(z) to the germ of the inverse-image
adjunction-unit section at the base-changed U and the prescribed changed point. The
coefficient is lifted only once. -/
theorem fieldChange_original_coefficient_germ
    (e : GaloisUnits.FieldMap k Ω K Ψ)
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (c : F.obj.obj (op U)) :
    let Q := (liftCoefficients.{u, w} (Spec (.of k))).obj F
    (fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q
        ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
          U (ULift.up z) Q.obj (ULift.up c)) =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap K Ψ)).toPresheafFiber
        ((smallEtaleBaseChange (fieldOriginalPullback k Ω K Ψ e)).obj U)
        (ULift.up (fieldChangeOriginalPoint k Ω K Ψ e U z))
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q).obj
        (((smallEtaleInverseImageAdjunction.{u, w}
          (fieldOriginalPullback k Ω K Ψ e)).unit.app Q).hom.app (op U) (ULift.up c)) :=
  fieldChangeUnderlyingStalkIso_original_germ_apply.{u, w} k Ω K Ψ e
    ((liftCoefficients.{u, w} (Spec (.of k))).obj F) U z (ULift.up c)

/-- For compatible field embeddings with prescribed closures and a sheaf morphism τ : F → F′ of
coefficient size w, let L be ULift^u. The natural stalk-module comparison ξ_e satisfies
(Φ_k⋙Res_χ)(Lτ)≫ξ_{LF′}.hom=ξ_{LF}.hom≫(f^*⋙Φ_K)(Lτ). The two sides retain the same lifted
coefficient morphism. -/
theorem fieldChange_original_coefficient_naturality
    (e : GaloisUnits.FieldMap k Ω K Ψ)
    {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}} (τ : F ⟶ F') :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
        GaloisUnits.restrictModules (GaloisUnits.FieldMap.restrictContinuous e)).map
          ((liftCoefficients.{u, w} (Spec (.of k))).map τ) ≫
        (fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F') =
      (fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F) ≫
        (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
          fieldGeometricStalkGaloisFunctor.{u, w} K Ψ).map
            ((liftCoefficients.{u, w} (Spec (.of k))).map τ) :=
  (fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.naturality
    ((liftCoefficients.{u, w} (Spec (.of k))).map τ)

end AlgebraicGeometry.Scheme.DerivedSections

end
