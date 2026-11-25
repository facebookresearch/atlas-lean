/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from Mathlib (leanprover-community/mathlib4, revision
fc4f59e577feb1a4956671bc04ac18aaaf8cd842):

`Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean`:
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Joël Riou

`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`:
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Joël Riou, Andrew Yang

Adapted portions: `pushforwardNatTrans`, `pushforwardCongr` and `pushforwardPushforwardAdj`
transpose `SheafOfModules.pushforwardNatTrans`, `SheafOfModules.pushforwardCongr` and
`SheafOfModules.pushforwardPushforwardAdj` (with their naturality and triangle proofs) from
sheaves to presheaves of modules; `presheafRestrictAdjunction` follows
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction`, including its two compatibility proofs.
-/

module

public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
public import MathlibExt.AlgebraicGeometry.SchemeModulesTensor

/-!
# Tensor products of line bundles

A tensor product of two line bundles on a scheme is a line bundle, and so is every tensor power
of a line bundle (`IsLineBundle.moduleTensor`, `IsLineBundle.power`). Here `moduleTensor` and
`power` are those of `SchemeModulesTensor`: the sheafified tensor product of the underlying
presheaves of modules, and its iterates.

The proof is local. Restriction to an open subscheme `U` of `X` commutes with the sheafified
tensor product (`restrictModuleTensorIso`), so trivializations of `L` and `M` on a common open
neighbourhood give one of `L ⊗ M` there, through `𝒪_U ⊗ 𝒪_U ≅ 𝒪_U` (`unitTensorUnitIso`).
The commutation has two parts.

* Restriction commutes with sheafification (`sheafificationRestrictIso`): both composites are
  left adjoint to the same functor. This uses the restriction–pushforward adjunction on
  presheaves of modules (`presheafRestrictAdjunction`), the presheaf counterpart of
  `Scheme.Modules.restrictAdjunction`.
* Restriction commutes with the tensor product of presheaves of modules
  (`pushforwardTensorIso`). It restricts scalars along the ring isomorphisms
  `𝒪_U(V) ≅ 𝒪_X(f(V))`, and restriction of scalars along a surjective map of commutative rings
  commutes with tensor products (`restrictScalarsTensorIso`).

## Main declarations

* `IsLineBundle.moduleTensor`, `IsLineBundle.power`.
* `restrictModuleTensorIso f L M`: `(L ⊗ M)|_U ≅ L|_U ⊗ M|_U` for an open immersion
  `f : U ⟶ X`.
* `sheafificationRestrictIso f`, `presheafRestrictAdjunction f`.
* `restrictScalarsTensorIso`, `pushforwardTensorIso`.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LineBundleTensor

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open _root_.AlgebraicGeometry

universe v u u₁ u₂ v₁ v₂

section PresheafPushforward

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A natural transformation `α : F ⟶ G` induces a natural transformation from the
pushforward of presheaves of modules along `G` to the pushforward along `F`. -/
def pushforwardNatTrans {F G : C ⥤ D} {S : Cᵒᵖ ⥤ RingCat.{u}} {R : Dᵒᵖ ⥤ RingCat.{u}}
    (φ : S ⟶ G.op ⋙ R) (α : F ⟶ G) :
    PresheafOfModules.pushforward.{v} φ ⟶
      PresheafOfModules.pushforward.{v} (φ ≫ Functor.whiskerRight (NatTrans.op α) R) where
  app M :=
  { app U := (ModuleCat.restrictScalars (φ.app U).hom).map (M.map (α.app U.unop).op)
    naturality {U V} i := by
      ext x
      dsimp
      change (M.presheaf.map (G.map i.unop).op ≫ M.presheaf.map (α.app V.unop).op) _ =
        (M.presheaf.map (α.app U.unop).op ≫ M.presheaf.map (F.map i.unop).op) _
      simp only [← CategoryTheory.Functor.map_comp, ← op_comp, α.naturality] }
  naturality {M N} f := by
    ext U x
    exact congr($(f.naturality (α.app U.unop).op) x).symm

/-- Pushforwards of presheaves of modules along equal ring maps are isomorphic. -/
def pushforwardCongr {F : C ⥤ D} {S : Cᵒᵖ ⥤ RingCat.{u}} {R : Dᵒᵖ ⥤ RingCat.{u}}
    {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ) :
    PresheafOfModules.pushforward.{v} φ ≅ PresheafOfModules.pushforward.{v} ψ :=
  NatIso.ofComponents (fun M ↦ PresheafOfModules.isoMk
      (fun U ↦ (ModuleCat.restrictScalarsCongr (by subst e; rfl)).app _)
      fun _ _ _ ↦ by subst e; rfl) fun _ ↦ by subst e; rfl

set_option backward.isDefEq.respectTransparency false in
/-- If `F ⊣ G`, the pushforwards of presheaves of modules along `F` and `G` are adjoint,
for compatible ring maps (the presheaf counterpart of
`SheafOfModules.pushforwardPushforwardAdj`). -/
def pushforwardPushforwardAdj {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {S : Cᵒᵖ ⥤ RingCat.{u}} {R : Dᵒᵖ ⥤ RingCat.{u}}
    (φ : S ⟶ F.op ⋙ R) (ψ : R ⟶ G.op ⋙ S)
    (H₁ : Functor.whiskerRight (NatTrans.op adj.counit) R = ψ ≫ G.op.whiskerLeft φ)
    (H₂ : φ ≫ F.op.whiskerLeft ψ ≫ Functor.whiskerRight (NatTrans.op adj.unit) S = 𝟙 S) :
    PresheafOfModules.pushforward.{v} φ ⊣ PresheafOfModules.pushforward.{v} ψ where
  unit := (PresheafOfModules.pushforwardId _).inv ≫ pushforwardNatTrans (𝟙 _) adj.counit ≫
      (pushforwardCongr (by simpa using H₁)).hom ≫
        (PresheafOfModules.pushforwardComp _ _).inv
  counit := (PresheafOfModules.pushforwardComp _ _).hom ≫ pushforwardNatTrans _ adj.unit ≫
      (pushforwardCongr (by simpa using H₂)).hom ≫ (PresheafOfModules.pushforwardId _).hom
  left_triangle_components M := by
    ext U x
    change (M.presheaf.map (adj.counit.app (F.obj U.unop)).op ≫
      M.presheaf.map (F.map (adj.unit.app U.unop)).op) _ = _
    dsimp only [Functor.id_obj]
    rw [← Functor.map_comp, ← op_comp, adj.left_triangle_components]
    simp
  right_triangle_components M := by
    ext U x
    change (M.presheaf.map (G.map (adj.counit.app U.unop)).op ≫
      M.presheaf.map (adj.unit.app (G.obj U.unop)).op) _ = _
    rw [← Functor.map_comp, ← op_comp, adj.right_triangle_components]
    simp

end PresheafPushforward

section RestrictScalarsTensor

/-! For a map `g : A ⟶ B` of commutative rings and a `B`-module `M`, write `M_A` for `M` viewed
as an `A`-module through `g` (`ModuleCat.restrictScalars g.hom`). -/

variable {A B : CommRingCat.{u}} (g : A ⟶ B)

/-- Restriction of scalars along a surjective (for instance bijective) map $g : A \to B$ of
commutative rings commutes with tensor products: for $B$-modules $M$ and $N$, the $A$-linear
isomorphism $M_A \otimes_A N_A \cong (M \otimes_B N)_A$, $m \otimes n \mapsto m \otimes n$. -/
def restrictScalarsTensorIso (hg : Function.Surjective g.hom) (M N : ModuleCat.{u} B) :
    (ModuleCat.restrictScalars g.hom).obj M ⊗ (ModuleCat.restrictScalars g.hom).obj N ≅
      (ModuleCat.restrictScalars g.hom).obj (M ⊗ N) :=
  letI : Algebra A B := g.hom.toAlgebra
  letI : Module A M := Module.compHom M g.hom
  letI : Module A N := Module.compHom N g.hom
  haveI : IsScalarTower A B M := ⟨fun a b m ↦ mul_smul (g.hom a) b m⟩
  haveI : IsScalarTower A B N := ⟨fun a b m ↦ mul_smul (g.hom a) b m⟩
  letI : TensorProduct.CompatibleSMul A B M N :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective M N hg
  (((TensorProduct.equivOfCompatibleSMul A B B M N).symm).restrictScalars A).toModuleIso

theorem restrictScalarsTensorIso_hom_tmul (hg : Function.Surjective g.hom)
    (M N : ModuleCat.{u} B) (m : (ModuleCat.restrictScalars g.hom).obj M)
    (n : (ModuleCat.restrictScalars g.hom).obj N) :
    (restrictScalarsTensorIso g hg M N).hom.hom (m ⊗ₜ[A] n) =
      TensorProduct.tmul B (M := M) (N := N) m n :=
  rfl

theorem restrictScalarsTensorIso_inv_tmul (hg : Function.Surjective g.hom)
    (M N : ModuleCat.{u} B) (m : M) (n : N) :
    (restrictScalarsTensorIso g hg M N).inv.hom (m ⊗ₜ[B] n : TensorProduct B M N) =
      TensorProduct.tmul A (M := (ModuleCat.restrictScalars g.hom).obj M)
        (N := (ModuleCat.restrictScalars g.hom).obj N) m n :=
  rfl

end RestrictScalarsTensor

section PushforwardTensor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (φ : S ⟶ F.op ⋙ R) [IsIso φ]

/-- Pushforward along an isomorphism of presheaves of commutative rings commutes with the
tensor product of presheaves of modules. -/
def pushforwardTensorIso (P Q : PresheafOfModulesOfCommRing.{u} R) :
    (PresheafOfModulesOfCommRing.pushforward φ).obj P ⊗
        (PresheafOfModulesOfCommRing.pushforward φ).obj Q ≅
      (PresheafOfModulesOfCommRing.pushforward φ).obj (P ⊗ Q) :=
  PresheafOfModules.isoMk
    (fun V ↦ restrictScalarsTensorIso (φ.app V)
      (ConcreteCategory.bijective_of_isIso (φ.app V)).2 (P.obj (F.op.obj V)) (Q.obj (F.op.obj V)))
    (fun _ _ _ ↦ ModuleCat.MonoidalCategory.tensor_ext fun _ _ ↦ rfl)

end PushforwardTensor

section Restriction

variable {X U : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f]

/-- The ring isomorphisms `𝒪_U(V) ≅ 𝒪_X(f(V))` along which restriction to `U` restricts
scalars. -/
def restrictRingHom : U.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
  { app V := (f.appIso V.unop).inv }

instance : IsIso (C := U.Opensᵒᵖ ⥤ CommRingCat.{u}) (restrictRingHom f) := by
  have (V : U.Opensᵒᵖ) : IsIso ((restrictRingHom f).app V) :=
    inferInstanceAs (IsIso (f.appIso V.unop).inv)
  exact NatIso.isIso_of_isIso_app _

/-- The ring map along which `Scheme.Modules.restrictFunctor f` restricts scalars. -/
abbrev restrictRingMap : U.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
  Functor.whiskerRight (restrictRingHom f) (forget₂ CommRingCat RingCat)

/-- Restriction of presheaves of modules along an open immersion. -/
abbrev presheafRestrict :
    PresheafOfModules.{u} X.ringCatSheaf.obj ⥤ PresheafOfModules.{u} U.ringCatSheaf.obj :=
  PresheafOfModules.pushforward (restrictRingMap f)

/-- Pushforward of presheaves of modules along a morphism of schemes. -/
abbrev presheafPushforward :
    PresheafOfModules.{u} U.ringCatSheaf.obj ⥤ PresheafOfModules.{u} X.ringCatSheaf.obj :=
  PresheafOfModules.pushforward f.toRingCatSheafHom.hom

/-- Restriction of presheaves of modules along an open immersion is left adjoint to the
pushforward. -/
def presheafRestrictAdjunction : presheafRestrict f ⊣ presheafPushforward f :=
  pushforwardPushforwardAdj (by exact f.isOpenEmbedding.isOpenMap.adjunction) _ _
    (by ext V x; congrm $((f.app_appIso_inv _).symm).hom x)
    (by
      ext V x
      have : (f.appIso V.unop).inv ≫ f.app _ ≫
          U.presheaf.map (eqToHom (f.preimage_image_eq V.unop).symm).op = 𝟙 _ := by
        rw [Scheme.Hom.appIso_inv_app_assoc, ← Functor.map_comp, ← U.presheaf.map_id]; rfl
      congrm $this x)

/-- The right adjoints of `sheafification ⋙ restrict` and `restrict ⋙ sheafification`
agree. -/
def rightAdjointIso :
    (SheafOfModules.forget U.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 U.ringCatSheaf.obj)) ⋙ presheafPushforward f ≅
      Scheme.Modules.pushforward f ⋙ (SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)) :=
  Iso.refl _

/-- Restriction along an open immersion commutes with sheafification of presheaves of
modules. -/
def sheafificationRestrictIso :
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj) ⋙
        Scheme.Modules.restrictFunctor f ≅
      presheafRestrict f ⋙ PresheafOfModules.sheafification (𝟙 U.ringCatSheaf.obj) :=
  Adjunction.leftAdjointUniq
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).comp
      (Scheme.Modules.restrictAdjunction f))
    (((presheafRestrictAdjunction f).comp
      (PresheafOfModules.sheafificationAdjunction (𝟙 U.ringCatSheaf.obj))).ofNatIsoRight
        (rightAdjointIso f))

/-- Restriction along an open immersion commutes with the tensor product of module sheaves. -/
def restrictModuleTensorIso (L M : X.Modules) :
    (SchemeModulesTensor.moduleTensor X L M).restrict f ≅
      SchemeModulesTensor.moduleTensor U (L.restrict f) (M.restrict f) :=
  (sheafificationRestrictIso f).app _ ≪≫
    (PresheafOfModules.sheafification (𝟙 U.ringCatSheaf.obj)).mapIso
      (pushforwardTensorIso (restrictRingHom f) L.val M.val).symm

end Restriction

section Assembly

variable {Y : Scheme.{u}}

/-- `moduleTensor` sends a pair of isomorphisms to an isomorphism. -/
def moduleTensorMapIso {L L' M M' : Y.Modules} (e : L ≅ L') (e' : M ≅ M') :
    SchemeModulesTensor.moduleTensor Y L M ≅ SchemeModulesTensor.moduleTensor Y L' M' :=
  (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).mapIso
    (tensorIso (C := PresheafOfModulesOfCommRing.{u} Y.sheaf.obj)
      ((SheafOfModules.forget _).mapIso e) ((SheafOfModules.forget _).mapIso e'))

variable (Y) in
/-- `𝒪_Y ⊗ 𝒪_Y ≅ 𝒪_Y`. -/
def unitTensorUnitIso :
    SchemeModulesTensor.moduleTensor Y (SheafOfModules.unit Y.ringCatSheaf)
        (SheafOfModules.unit Y.ringCatSheaf) ≅ SheafOfModules.unit Y.ringCatSheaf :=
  (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).mapIso
      (λ_ (𝟙_ (PresheafOfModulesOfCommRing.{u} Y.sheaf.obj))) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).counit).app
      (SheafOfModules.unit Y.ringCatSheaf)

/-- A trivialization of `L` on `V` restricts to a trivialization on any `W ≤ V`. -/
def restrictTrivializationOfLE (L : Y.Modules) {V W : Y.Opens} (h : W ≤ V)
    (e : L.restrict V.ι ≅ CoherentCurveLinearSeries.structureModule V) :
    L.restrict W.ι ≅ CoherentCurveLinearSeries.structureModule W :=
  (Scheme.Modules.restrictFunctorCongr (Y.homOfLE_ι h).symm).app L ≪≫
    (Scheme.Modules.restrictFunctorComp (Y.homOfLE h) V.ι).app L ≪≫
    (Scheme.Modules.restrictFunctor (Y.homOfLE h)).mapIso e ≪≫
    Scheme.Modules.restrictUnitIso (Y.homOfLE h)

open CoherentCurveLinearSeries in
/-- `IsLineBundle`, with restrictions in place of pullbacks along open immersions. -/
theorem isLineBundle_iff_restrict (L : Y.Modules) :
    IsLineBundle L ↔ ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧
      Nonempty (L.restrict V.ι ≅ CoherentCurveLinearSeries.structureModule V) := by
  refine forall_congr' fun y ↦ exists_congr fun V ↦ and_congr_right fun _ ↦ ?_
  exact ⟨fun ⟨e⟩ ↦ ⟨(Scheme.Modules.restrictFunctorIsoPullback V.ι).app L ≪≫ e⟩,
    fun ⟨e⟩ ↦ ⟨((Scheme.Modules.restrictFunctorIsoPullback V.ι).app L).symm ≪≫ e⟩⟩

end Assembly

end MathlibExt.AlgebraicGeometry.LineBundleTensor

namespace MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

open CategoryTheory _root_.AlgebraicGeometry LineBundleTensor SchemeModulesTensor

universe u

variable {Y : Scheme.{u}}

/-- The tensor product of two line bundles is a line bundle. -/
theorem IsLineBundle.moduleTensor {L M : Y.Modules} (hL : IsLineBundle L)
    (hM : IsLineBundle M) : IsLineBundle (moduleTensor Y L M) := by
  rw [isLineBundle_iff_restrict] at hL hM ⊢
  intro y
  obtain ⟨V, hyV, ⟨eL⟩⟩ := hL y
  obtain ⟨V', hyV', ⟨eM⟩⟩ := hM y
  exact ⟨V ⊓ V', ⟨hyV, hyV'⟩, ⟨restrictModuleTensorIso (V ⊓ V').ι L M ≪≫
    moduleTensorMapIso (restrictTrivializationOfLE L inf_le_left eL)
      (restrictTrivializationOfLE M inf_le_right eM) ≪≫ unitTensorUnitIso _⟩⟩

/-- Tensor powers of a line bundle are line bundles. -/
theorem IsLineBundle.power {L : Y.Modules} (hL : IsLineBundle L) (n : ℕ) :
    IsLineBundle (power L n) := by
  induction n with
  | zero => exact isLineBundle_structureModule Y
  | succ n ih => exact ih.moduleTensor hL

end MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
