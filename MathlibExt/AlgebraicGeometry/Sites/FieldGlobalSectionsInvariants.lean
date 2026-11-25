/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module
public import MathlibExt.CategoryTheory.Action.Invariants
public import MathlibExt.AlgebraicGeometry.Sites.FieldModuleCohomologyCategory
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleCoefficientSections
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Comma.Over.Basic

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- The source's actual original identity étale object. -/
abbrev fieldIdentityEtale : (Spec (.of k)).Etale := Scheme.Etale.mk (𝟙 (Spec (.of k)))

/-- Its actual prescribed geometric point is the original spectrum algebra map. -/
def fieldTerminalFiberPoint :
    (fieldGeometricPoint k Ω).fiber.obj (fieldIdentityEtale k) :=
  show Over.mk (Spec.algebraMap k Ω) ⟶ Over.mk (𝟙 (Spec (.of k))) from
    Over.homMk (Spec.algebraMap k Ω)

theorem fieldTerminalFiberPoint_left :
    (fieldTerminalFiberPoint k Ω).left = Spec.algebraMap k Ω := rfl

instance fieldTerminalFiber_subsingleton :
    Subsingleton ((fieldGeometricPoint k Ω).fiber.obj (fieldIdentityEtale k)) := by
  change Subsingleton (Over.mk (Spec.algebraMap k Ω) ⟶ Over.mk (𝟙 (Spec (.of k))))
  exact ⟨fun f g => (Over.mkIdTerminal (X := Spec (.of k))).hom_ext f g⟩

theorem fieldTerminalFiberPoint_fixed (g : Gal(Ω/k)) :
    g • fieldTerminalFiberPoint k Ω = fieldTerminalFiberPoint k Ω :=
  Subsingleton.elim _ _

/-- Evaluation at the SAME original terminal point, with the actual constant inverse. -/
def fieldTerminalFunctionsInvariantsEquiv (M : FieldCohomologyModule.{u, w} k Ω) :
    FieldEquivariantFunctions.{u, w} k Ω (fieldIdentityEtale k) M ≃+
      DiscreteAbelianAction.invariantsFunctor.obj M where
  toFun h := ⟨h (fieldTerminalFiberPoint k Ω), fun g => by
    change g • h (fieldTerminalFiberPoint k Ω) = h (fieldTerminalFiberPoint k Ω)
    calc
      _ = h (g • fieldTerminalFiberPoint k Ω) := (h.map_smul g _).symm
      _ = h (fieldTerminalFiberPoint k Ω) :=
        congrArg h (fieldTerminalFiberPoint_fixed k Ω g)⟩
  invFun m :=
    { toFun := fun _ => (show DiscreteAbelianAction.underlying M from m.val)
      map_smul' := fun g _ => by
        change m.val = (DiscreteAbelianAction.toTopRep.obj M).ρ g m.val
        exact (m.property g).symm }
  left_inv h := by
    ext z
    exact congrArg h (Subsingleton.elim _ _)
  right_inv m := by
    apply Subtype.ext
    rfl
  map_add' h h' := by
    apply Subtype.ext
    rfl

theorem fieldTerminalFunctionsInvariantsEquiv_val
    (M : FieldCohomologyModule.{u, w} k Ω)
    (h : FieldEquivariantFunctions.{u, w} k Ω (fieldIdentityEtale k) M) :
    (fieldTerminalFunctionsInvariantsEquiv.{u, w} k Ω M h).val =
      h (fieldTerminalFiberPoint k Ω) := rfl

theorem fieldTerminalFunctionsInvariantsEquiv_symm_apply
    (M : FieldCohomologyModule.{u, w} k Ω)
    (m : DiscreteAbelianAction.invariantsFunctor.obj M)
    (z : (fieldGeometricPoint k Ω).fiber.obj (fieldIdentityEtale k)) :
    (fieldTerminalFunctionsInvariantsEquiv.{u, w} k Ω M).symm m z = m.val := rfl

theorem fieldTerminalFunctionsInvariantsEquiv_naturality
    {M N : FieldCohomologyModule.{u, w} k Ω} (f : M ⟶ N)
    (h : FieldEquivariantFunctions.{u, w} k Ω (fieldIdentityEtale k) M) :
    fieldTerminalFunctionsInvariantsEquiv.{u, w} k Ω N
      (((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map f).hom.app
        (op (fieldIdentityEtale k)) h) =
    (DiscreteAbelianAction.invariantsFunctor.map f)
      (fieldTerminalFunctionsInvariantsEquiv.{u, w} k Ω M h) := by
  apply Subtype.ext
  rfl

/-- The actual original global-sections normalization at the identity object. -/
abbrev fieldGammaSectionsIso :
    Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} ≅
      (sheafSections (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).obj
        (op (fieldIdentityEtale k)) :=
  Sheaf.ΓNatIsoSheafSections _ _ (identityEtaleIsTerminal (Spec (.of k)))

/-- A component is exactly the fixed original unit followed by original-point evaluation. -/
def fieldGlobalSectionsInvariantsEquiv
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).obj Q ≃+
      DiscreteAbelianAction.invariantsFunctor.obj
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) :=
  ((fieldGammaSectionsIso.{u, w} k).app Q).addCommGroupIsoToAddEquiv.trans
    ((((sheafSections (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).obj
        (op (fieldIdentityEtale k))).mapIso
          ((fieldSheafGaloisEquivalence.{u, w} k Ω).unitIso.app Q)).addCommGroupIsoToAddEquiv.trans
      (fieldTerminalFunctionsInvariantsEquiv.{u, w} k Ω
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)))

theorem fieldGlobalSectionsInvariantsEquiv_naturality
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : Q ⟶ Q')
    (c : (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).obj Q) :
    fieldGlobalSectionsInvariantsEquiv.{u, w} k Ω Q'
      ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).map f c) =
      (DiscreteAbelianAction.invariantsFunctor.map
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map f))
        (fieldGlobalSectionsInvariantsEquiv.{u, w} k Ω Q c) := by
  let U := fieldIdentityEtale k
  let s := (fieldGammaSectionsIso.{u, w} k).hom.app Q c
  have hg := ConcreteCategory.congr_hom ((fieldGammaSectionsIso.{u, w} k).hom.naturality f) c
  change (fieldGammaSectionsIso.{u, w} k).hom.app Q'
    ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).map f c) =
    f.hom.app (op U) s at hg
  have hu := congrArg
    (fun a : Q ⟶ (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q') => a.hom.app (op U) s)
    ((fieldSheafGaloisEquivalence.{u, w} k Ω).unitIso.hom.naturality f)
  change ((fieldSheafGaloisEquivalence.{u, w} k Ω).unitIso.hom.app Q').hom.app (op U)
    (f.hom.app (op U) s) =
    (((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map f)).hom.app (op U))
      (((fieldSheafGaloisEquivalence.{u, w} k Ω).unitIso.hom.app Q).hom.app (op U) s) at hu
  apply Subtype.ext
  change (show FieldEquivariantFunctions.{u, w} k Ω U
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q') from
    (((fieldSheafGaloisEquivalence.{u, w} k Ω).unitIso.hom.app Q').hom.app (op U)
      ((fieldGammaSectionsIso.{u, w} k).hom.app Q'
        ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).map f c))))
          (fieldTerminalFiberPoint k Ω) = _
  rw [hg, hu]
  rfl

/-- The ONE natural isomorphism for the SAME actual Γ, T and literal invariant functor. -/
def fieldGlobalSectionsInvariantsIso :
    Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} ≅
      fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙ DiscreteAbelianAction.invariantsFunctor :=
  NatIso.ofComponents
    (fun Q =>
      { hom := AddCommGrpCat.ofHom
          (fieldGlobalSectionsInvariantsEquiv.{u, w} k Ω Q).toAddMonoidHom
        inv := AddCommGrpCat.ofHom
          (fieldGlobalSectionsInvariantsEquiv.{u, w} k Ω Q).symm.toAddMonoidHom })
    (fun f => by
      ext c
      exact fieldGlobalSectionsInvariantsEquiv_naturality.{u, w} k Ω f c)

theorem fieldGlobalSectionsInvariantsIso_germ
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (c : (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).obj Q) :
    (((fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app Q) c).val =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        (fieldIdentityEtale k) (ULift.up (fieldTerminalFiberPoint k Ω)) Q.obj
          ((fieldGammaSectionsIso.{u, w} k).hom.app Q c) := by
  exact fieldSheafGaloisEquivalence_unit_germ.{u, w} k Ω Q
    (fieldIdentityEtale k) (fieldTerminalFiberPoint k Ω)
      ((fieldGammaSectionsIso.{u, w} k).hom.app Q c)

theorem fieldGlobalSectionsInvariantsIso_inv_section
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (m : DiscreteAbelianAction.invariantsFunctor.obj
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)) :
    (fieldGammaSectionsIso.{u, w} k).hom.app Q
      ((fieldGlobalSectionsInvariantsIso.{u, w} k Ω).inv.app Q m) =
    ((fieldSheafGaloisEquivalence.{u, w} k Ω).unitIso.inv.app Q).hom.app
      (op (fieldIdentityEtale k))
      ((fieldTerminalFunctionsInvariantsEquiv.{u, w} k Ω
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)).symm m) := by
  let a := ((fieldGammaSectionsIso.{u, w} k).app Q).addCommGroupIsoToAddEquiv
  change a (a.symm _) = _
  rw [a.apply_symm_apply]
  rfl

theorem fieldGlobalSectionsInvariantsIso_hom_inv
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (m : DiscreteAbelianAction.invariantsFunctor.obj
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)) :
    (fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app Q
      ((fieldGlobalSectionsInvariantsIso.{u, w} k Ω).inv.app Q m) = m :=
  (fieldGlobalSectionsInvariantsEquiv.{u, w} k Ω Q).apply_symm_apply m

theorem fieldGlobalSectionsInvariantsIso_inv_hom
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (c : (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).obj Q) :
    (fieldGlobalSectionsInvariantsIso.{u, w} k Ω).inv.app Q
      ((fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app Q c) = c :=
  (fieldGlobalSectionsInvariantsEquiv.{u, w} k Ω Q).symm_apply_apply c

theorem fieldGlobalSectionsInvariantsIso_naturality
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : Q ⟶ Q') :
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).map f ≫
        (fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app Q' =
      (fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app Q ≫
        DiscreteAbelianAction.invariantsFunctor.map
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map f) :=
  (fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.naturality f

/-- Every original coefficient section uses exactly one actual L.obj F. -/
def originalFieldSectionsInvariantsEquiv
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}) :
    F.obj.obj (op (fieldIdentityEtale k)) ≃+
      DiscreteAbelianAction.invariantsFunctor.obj
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F)) :=
  AddEquiv.ulift.symm.trans
    (((fieldGammaSectionsIso.{u, w} k).app
      ((liftCoefficients.{u, w} (Spec (.of k))).obj F)).addCommGroupIsoToAddEquiv.symm.trans
        ((fieldGlobalSectionsInvariantsIso.{u, w} k Ω).app
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F)).addCommGroupIsoToAddEquiv)

theorem originalFieldSectionsInvariantsEquiv_germ
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (c : F.obj.obj (op (fieldIdentityEtale k))) :
    (originalFieldSectionsInvariantsEquiv.{u, w} k Ω F c).val =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        (fieldIdentityEtale k) (ULift.up (fieldTerminalFiberPoint k Ω))
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F).obj (ULift.up c) := by
  let Q := (liftCoefficients.{u, w} (Spec (.of k))).obj F
  let a := ((fieldGammaSectionsIso.{u, w} k).app Q).addCommGroupIsoToAddEquiv
  have h : a (a.symm (ULift.up c)) = ULift.up c := a.apply_symm_apply _
  have h0 : (originalFieldSectionsInvariantsEquiv.{u, w} k Ω F c).val =
      (((fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app Q)
        (a.symm (ULift.up c))).val := rfl
  have h1 := fieldGlobalSectionsInvariantsIso_germ.{u, w} k Ω Q
    (a.symm (ULift.up c))
  have h2 := congrArg
    (fun x : Q.obj.obj (op (fieldIdentityEtale k)) =>
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        (fieldIdentityEtale k) (ULift.up (fieldTerminalFiberPoint k Ω)) Q.obj x) h
  exact h0.trans (h1.trans h2)


/-- The original native section and the actual common Γ normalization are tied by one lift. -/
theorem originalFieldSectionsInvariantsEquiv_normalization
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (c : F.obj.obj (op (fieldIdentityEtale k))) :
    originalFieldSectionsInvariantsEquiv.{u, w} k Ω F c =
      (fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F)
        ((fieldGammaSectionsIso.{u, w} k).inv.app
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F) (ULift.up c)) := rfl

/-- The original inverse removes exactly that lift after the SAME unit inverse. -/
theorem originalFieldSectionsInvariantsEquiv_inv
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (m : DiscreteAbelianAction.invariantsFunctor.obj
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F))) :
    (originalFieldSectionsInvariantsEquiv.{u, w} k Ω F).symm m =
      (((fieldSheafGaloisEquivalence.{u, w} k Ω).unitIso.inv.app
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F)).hom.app
          (op (fieldIdentityEtale k))
          ((fieldTerminalFunctionsInvariantsEquiv.{u, w} k Ω
            ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
              ((liftCoefficients.{u, w} (Spec (.of k))).obj F))).symm m)).down := by
  let Q := (liftCoefficients.{u, w} (Spec (.of k))).obj F
  have h := fieldGlobalSectionsInvariantsIso_inv_section.{u, w} k Ω Q m
  exact congrArg (fun c : Q.obj.obj (op (fieldIdentityEtale k)) => c.down) h

/-- Every original sheaf arrow induces its actual original invariant coefficient arrow. -/
theorem originalFieldSectionsInvariantsEquiv_naturality
    {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}}
    (f : F ⟶ F') (c : F.obj.obj (op (fieldIdentityEtale k))) :
    originalFieldSectionsInvariantsEquiv.{u, w} k Ω F'
      (f.hom.app (op (fieldIdentityEtale k)) c) =
      DiscreteAbelianAction.invariantsFunctor.map
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
          ((liftCoefficients.{u, w} (Spec (.of k))).map f))
        (originalFieldSectionsInvariantsEquiv.{u, w} k Ω F c) := by
  let Q := (liftCoefficients.{u, w} (Spec (.of k))).obj F
  let Q' := (liftCoefficients.{u, w} (Spec (.of k))).obj F'
  let t := (liftCoefficients.{u, w} (Spec (.of k))).map f
  let x := (fieldGammaSectionsIso.{u, w} k).inv.app Q (ULift.up c)
  have h := ConcreteCategory.congr_hom ((fieldGammaSectionsIso.{u, w} k).inv.naturality t)
    (ULift.up c)
  change (fieldGammaSectionsIso.{u, w} k).inv.app Q'
    (ULift.up (f.hom.app (op (fieldIdentityEtale k)) c)) =
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).map t x at h
  have hn := fieldGlobalSectionsInvariantsEquiv_naturality.{u, w} k Ω t x
  change (fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app Q'
    ((fieldGammaSectionsIso.{u, w} k).inv.app Q'
      (ULift.up (f.hom.app (op (fieldIdentityEtale k)) c))) = _
  exact (congrArg ((fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app Q') h).trans hn

/-- An invariant coefficient defines a genuine global section of the SAME original inverse sheaf. -/
def fieldInvariantConstantGlobalSection (M : FieldCohomologyModule.{u, w} k Ω)
    (m : DiscreteAbelianAction.invariantsFunctor.obj M) :
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).obj
      ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M) :=
  (fieldGammaSectionsIso.{u, w} k).inv.app
    ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M)
    ((fieldTerminalFunctionsInvariantsEquiv.{u, w} k Ω M).symm m)

/-- The SAME original counit recovers every original invariant coefficient. -/
theorem fieldGlobalSectionsInvariants_counit_constant
    (M : FieldCohomologyModule.{u, w} k Ω)
    (m : DiscreteAbelianAction.invariantsFunctor.obj M) :
    DiscreteAbelianAction.invariantsFunctor.map
      ((fieldSheafGaloisEquivalence.{u, w} k Ω).counitIso.hom.app M)
      ((fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app
        ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M)
        (fieldInvariantConstantGlobalSection.{u, w} k Ω M m)) = m := by
  let Q := (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M
  let h := (fieldTerminalFunctionsInvariantsEquiv.{u, w} k Ω M).symm m
  let a := ((fieldGammaSectionsIso.{u, w} k).app Q).addCommGroupIsoToAddEquiv
  have hΓ : a (a.symm h) = h := a.apply_symm_apply h
  have hg := fieldGlobalSectionsInvariantsIso_germ.{u, w} k Ω Q (a.symm h)
  have ht := congrArg
    (fun s : Q.obj.obj (op (fieldIdentityEtale k)) =>
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        (fieldIdentityEtale k) (ULift.up (fieldTerminalFiberPoint k Ω)) Q.obj s) hΓ
  have hh := hg.trans ht
  have hc := fieldSheafGaloisEquivalence_counit_germ.{u, w} k Ω M
    (fieldIdentityEtale k) (fieldTerminalFiberPoint k Ω) h
  apply Subtype.ext
  change DiscreteAbelianAction.homToAdd
    ((fieldSheafGaloisEquivalence.{u, w} k Ω).counitIso.hom.app M)
    (((fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app Q) (a.symm h)).val = m.val
  exact (congrArg (DiscreteAbelianAction.homToAdd
    ((fieldSheafGaloisEquivalence.{u, w} k Ω).counitIso.hom.app M)) hh).trans hc

/-- The complete source unit fixes actual objects, both maps, and every original normalization. -/
structure OriginalFieldGlobalSectionsInvariantsLaws : Prop where
  literal_invariants : ∀ (M : FieldCohomologyModule.{u, w} k Ω)
    (m : DiscreteAbelianAction.underlying M),
    m ∈ DiscreteAbelianAction.invariants M ↔ ∀ g : Gal(Ω/k), g • m = m
  coefficient_maps : ∀ (M N : FieldCohomologyModule.{u, w} k Ω) (f : M ⟶ N)
    (m : DiscreteAbelianAction.invariantsFunctor.obj M),
    (DiscreteAbelianAction.invariantsFunctor.map f m).val =
      DiscreteAbelianAction.homToAdd f m.val
  original_point : (fieldTerminalFiberPoint k Ω).left = Spec.algebraMap k Ω
  original_point_fixed : ∀ g : Gal(Ω/k),
    g • fieldTerminalFiberPoint k Ω = fieldTerminalFiberPoint k Ω
  terminal_evaluation : ∀ (M : FieldCohomologyModule.{u, w} k Ω)
    (h : FieldEquivariantFunctions.{u, w} k Ω (fieldIdentityEtale k) M),
    (fieldTerminalFunctionsInvariantsEquiv.{u, w} k Ω M h).val =
      h (fieldTerminalFiberPoint k Ω)
  terminal_inverse : ∀ (M : FieldCohomologyModule.{u, w} k Ω)
    (m : DiscreteAbelianAction.invariantsFunctor.obj M)
    (z : (fieldGeometricPoint k Ω).fiber.obj (fieldIdentityEtale k)),
    (fieldTerminalFunctionsInvariantsEquiv.{u, w} k Ω M).symm m z = m.val
  natural_iso : Nonempty (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} ≅
    fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙ DiscreteAbelianAction.invariantsFunctor)
  forward_original_germ : ∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (c : (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).obj Q),
    (((fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app Q) c).val =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        (fieldIdentityEtale k) (ULift.up (fieldTerminalFiberPoint k Ω)) Q.obj
        ((fieldGammaSectionsIso.{u, w} k).hom.app Q c)
  inverse_original_unit : ∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (m : DiscreteAbelianAction.invariantsFunctor.obj
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)),
    (fieldGammaSectionsIso.{u, w} k).hom.app Q
      ((fieldGlobalSectionsInvariantsIso.{u, w} k Ω).inv.app Q m) =
      ((fieldSheafGaloisEquivalence.{u, w} k Ω).unitIso.inv.app Q).hom.app
        (op (fieldIdentityEtale k))
        ((fieldTerminalFunctionsInvariantsEquiv.{u, w} k Ω
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)).symm m)
  hom_inv : ∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (m : DiscreteAbelianAction.invariantsFunctor.obj
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)),
    (fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app Q
      ((fieldGlobalSectionsInvariantsIso.{u, w} k Ω).inv.app Q m) = m
  inv_hom : ∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (c : (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).obj Q),
    (fieldGlobalSectionsInvariantsIso.{u, w} k Ω).inv.app Q
      ((fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app Q c) = c
  original_sheaf_naturality : ∀
    (Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (f : Q ⟶ Q'),
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).map f ≫
      (fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app Q' =
      (fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app Q ≫
        DiscreteAbelianAction.invariantsFunctor.map
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map f)
  inverse_module_naturality : ∀ (M N : FieldCohomologyModule.{u, w} k Ω) (f : M ⟶ N)
    (h : FieldEquivariantFunctions.{u, w} k Ω (fieldIdentityEtale k) M),
    fieldTerminalFunctionsInvariantsEquiv.{u, w} k Ω N
      (((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map f).hom.app
        (op (fieldIdentityEtale k)) h) =
      DiscreteAbelianAction.invariantsFunctor.map f
        (fieldTerminalFunctionsInvariantsEquiv.{u, w} k Ω M h)
  one_original_lift : ∀ (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (c : F.obj.obj (op (fieldIdentityEtale k))),
    originalFieldSectionsInvariantsEquiv.{u, w} k Ω F c =
      (fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F)
        ((fieldGammaSectionsIso.{u, w} k).inv.app
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F) (ULift.up c))
  original_lifted_germ : ∀ (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (c : F.obj.obj (op (fieldIdentityEtale k))),
    (originalFieldSectionsInvariantsEquiv.{u, w} k Ω F c).val =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        (fieldIdentityEtale k) (ULift.up (fieldTerminalFiberPoint k Ω))
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F).obj (ULift.up c)
  original_lifted_inverse : ∀ (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (m : DiscreteAbelianAction.invariantsFunctor.obj
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F))),
    (originalFieldSectionsInvariantsEquiv.{u, w} k Ω F).symm m =
      (((fieldSheafGaloisEquivalence.{u, w} k Ω).unitIso.inv.app
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F)).hom.app
          (op (fieldIdentityEtale k))
          ((fieldTerminalFunctionsInvariantsEquiv.{u, w} k Ω
            ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
              ((liftCoefficients.{u, w} (Spec (.of k))).obj F))).symm m)).down
  every_original_map : ∀ (F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (f : F ⟶ F') (c : F.obj.obj (op (fieldIdentityEtale k))),
    originalFieldSectionsInvariantsEquiv.{u, w} k Ω F'
      (f.hom.app (op (fieldIdentityEtale k)) c) =
      DiscreteAbelianAction.invariantsFunctor.map
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
          ((liftCoefficients.{u, w} (Spec (.of k))).map f))
        (originalFieldSectionsInvariantsEquiv.{u, w} k Ω F c)
  same_counit_recovery : ∀ (M : FieldCohomologyModule.{u, w} k Ω)
    (m : DiscreteAbelianAction.invariantsFunctor.obj M),
    DiscreteAbelianAction.invariantsFunctor.map
      ((fieldSheafGaloisEquivalence.{u, w} k Ω).counitIso.hom.app M)
      ((fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app
        ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M)
        (fieldInvariantConstantGlobalSection.{u, w} k Ω M m)) = m

/-- Original Γ is naturally the SAME geometric-module invariant subgroup, with all source maps. -/
theorem original_field_global_sections_invariants :
    OriginalFieldGlobalSectionsInvariantsLaws.{u, w} k Ω where
  literal_invariants := DiscreteAbelianAction.mem_invariants
  coefficient_maps := fun _ _ f m => DiscreteAbelianAction.invariantsFunctor_map_val f m
  original_point := fieldTerminalFiberPoint_left k Ω
  original_point_fixed := fieldTerminalFiberPoint_fixed k Ω
  terminal_evaluation := fieldTerminalFunctionsInvariantsEquiv_val.{u, w} k Ω
  terminal_inverse := fieldTerminalFunctionsInvariantsEquiv_symm_apply.{u, w} k Ω
  natural_iso := ⟨fieldGlobalSectionsInvariantsIso.{u, w} k Ω⟩
  forward_original_germ := fieldGlobalSectionsInvariantsIso_germ.{u, w} k Ω
  inverse_original_unit := fieldGlobalSectionsInvariantsIso_inv_section.{u, w} k Ω
  hom_inv := fieldGlobalSectionsInvariantsIso_hom_inv.{u, w} k Ω
  inv_hom := fieldGlobalSectionsInvariantsIso_inv_hom.{u, w} k Ω
  original_sheaf_naturality := fun _ _ f => fieldGlobalSectionsInvariantsIso_naturality.{u, w} k Ω f
  inverse_module_naturality := fun _ _ f h =>
    fieldTerminalFunctionsInvariantsEquiv_naturality.{u, w} k Ω f h
  one_original_lift := originalFieldSectionsInvariantsEquiv_normalization.{u, w} k Ω
  original_lifted_germ := originalFieldSectionsInvariantsEquiv_germ.{u, w} k Ω
  original_lifted_inverse := originalFieldSectionsInvariantsEquiv_inv.{u, w} k Ω
  every_original_map := fun _ _ f c =>
    originalFieldSectionsInvariantsEquiv_naturality.{u, w} k Ω f c
  same_counit_recovery := fieldGlobalSectionsInvariants_counit_constant.{u, w} k Ω

end AlgebraicGeometry.Scheme.DerivedSections
