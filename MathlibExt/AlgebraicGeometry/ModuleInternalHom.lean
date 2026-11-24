/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/InternalHom.lean`
(AxiomMath/Stacks, https://github.com/AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b):
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source files carry no per-file copyright notice or author list.
Modified: source-only citation attributes removed; the construction and its proofs
are placed in this namespace.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafHom

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The internal hom of presheaves of modules

Let `C` be a site with Grothendieck topology `J` and let `O` be a presheaf of commutative rings
on `C`. For presheaves of `O`-modules `F` and `G`, the internal hom `𝓗om_O(F, G)` is the
presheaf of `O`-modules whose value at `U` is the `O(U)`-module `Hom_{O|_U}(F|_U, G|_U)` of
morphisms of modules over the localized ring `O|_U` on the slice category `C/U`, with
restriction maps given by relocalization along `Over.map f` and with `O(U)` acting by
multiplication by the restrictions of a section. If `G` is a sheaf, then so is `𝓗om_O(F, G)`.

## Main definitions

* `ORestr`: the localized ring `O|_U` on the slice category `C/U`.
* `restrFun`: the restriction functor `F ↦ F|_U` from `O`-modules to `O|_U`-modules.
* `homRestr`: the restriction `F|_V ⟶ G|_V` of a morphism `F|_U ⟶ G|_U` along `V ⟶ U`.
* `homModule`: the `O(U)`-module structure on `Hom_{O|_U}(F|_U, G|_U)`.
* `internalHom`: the internal hom presheaf `𝓗om_O(F, G)`.
* `IsCompatibleFamily`: compatibility of a family of local morphisms indexed by a cover.
* `restrictToCover`: the family of restrictions of a morphism to the members of a cover.

## Main results

* `internalHom_glue`: for every cover `S` of `U`, `restrictToCover` is a bijection from
  morphisms `F|_U ⟶ G|_U` onto compatible families of local morphisms, provided `G` is a sheaf.
* `internalHom_isSheaf`: if `G` is a sheaf, then `internalHom O F G` is a sheaf.

## Implementation notes

The ring `O` is valued in commutative rings, which is needed for multiplication by a section
to be `O|_U`-linear. The presheaf of rings underlying the modules is
`Oforget O = O ⋙ forget₂ CommRingCat RingCat`. The ring `O` itself need not be a sheaf.

The four universes, of the objects and morphisms of `C`, of the ring `O` and of the modules `F`
and `G`, are independent: `presheafHom` places no constraint between the universes of `C` and of
the target category, and the gluing argument only uses the sheaf condition for `G` on the slice
site. In particular the module universe is not tied to `max u v`.

The gluing is done on underlying abelian presheaves: the presheaf of morphisms `F|_W ⟶ G|_W`
glues over the slice site because `G|_U` is a sheaf, and the glued morphism is then upgraded to
an `O|_U`-linear morphism via `PresheafOfModules.homMk`.

## References

* [Stacks: Modules on Sites, Section 18.27](https://stacks.math.columbia.edu/tag/04TT)
-/

open CategoryTheory Opposite

namespace MathlibExt.AlgebraicGeometry.ModuleInternalHom

universe v u t

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat)

/-- The underlying presheaf of (possibly noncommutative) rings of `O`, obtained by
forgetting commutativity. This is the presheaf of rings consumed by `PresheafOfModules`. -/
noncomputable abbrev Oforget : Cᵒᵖ ⥤ RingCat := O ⋙ forget₂ CommRingCat RingCat

/-- The restricted presheaf of rings `O|_U` on the slice category `C/U`: the composition of `O`
with the localization functor `Over.forget U`. -/
noncomputable def ORestr (U : C) : (Over U)ᵒᵖ ⥤ RingCat := (Over.forget U).op ⋙ Oforget O

/-- The restriction functor `PMod(O) ⥤ PMod(O|_U)` sending an `O`-module to its restriction
`F|_U` on `C/U`. -/
noncomputable def restrFun (U : C) :
    PresheafOfModules (Oforget O) ⥤ PresheafOfModules (ORestr O U) :=
  PresheafOfModules.pushforward (𝟙 (ORestr O U))

/-- For `f : V ⟶ U`, the restricted ring `O|_V` is the pullback of `O|_U` along the
relocalization functor `Over.map f : C/V ⥤ C/U`. -/
theorem ORestr_reloc {V U : C} (f : V ⟶ U) :
    ORestr O V = (Over.map f).op ⋙ ORestr O U := by
  have h : (Over.map f).op ⋙ (Over.forget U).op = (Over.forget V).op := by
    have : (Over.map f).op ⋙ (Over.forget U).op = (Over.map f ⋙ Over.forget U).op :=
      Functor.toPrefunctor_injective rfl
    rw [this, Over.mapForget_eq]
  dsimp only [ORestr, Oforget]
  rw [← Functor.assoc, ← Functor.assoc, h, Functor.assoc]

/-- The relocalization functor `PMod(O|_U) ⥤ PMod(O|_V)` induced by a morphism `f : V ⟶ U`,
restricting along `Over.map f : C/V ⥤ C/U`. -/
noncomputable def relocRestr {V U : C} (f : V ⟶ U) :
    PresheafOfModules (ORestr O U) ⥤ PresheafOfModules (ORestr O V) :=
  PresheafOfModules.pushforward (eqToHom (ORestr_reloc O f))

variable (F G : PresheafOfModules.{t} (Oforget O))

/-- Relocalizing `M|_U` along `f : V ⟶ U` gives `M|_V`. -/
theorem reloc_restr_obj (M : PresheafOfModules (Oforget O)) {V U : C} (f : V ⟶ U) :
    (relocRestr O f).obj ((restrFun O U).obj M) = (restrFun O V).obj M := rfl

/-- The restriction along `f : V ⟶ U` of a morphism `α : F|_U ⟶ G|_U` of `O|_U`-modules, as a
morphism `F|_V ⟶ G|_V` obtained by relocalizing along `Over.map f`. -/
noncomputable def homRestr {V U : C} (f : V ⟶ U)
    (α : (restrFun O U).obj F ⟶ (restrFun O U).obj G) :
    (restrFun O V).obj F ⟶ (restrFun O V).obj G :=
  eqToHom (reloc_restr_obj O F f).symm ≫ (relocRestr O f).map α ≫ eqToHom (reloc_restr_obj O G f)

/-- The restriction of a section `f ∈ O(U)` to an object `V` of the slice category
`C/U`, i.e. its image in `O|_U(V) = O(V.left)` under the restriction map of `O`. -/
noncomputable def fRestr (U : C) (f : (Oforget O).obj (op U)) (V : (Over U)ᵒᵖ) :
    (ORestr O U).obj V :=
  ((Oforget O).map (V.unop.hom).op).hom f

/-- Multiplication by the restriction of a section `f ∈ O(U)` commutes with the action of
`O|_U(V)` on `G|_U(V)`. -/
theorem multEndo_smul_comm (U : C) (f : (Oforget O).obj (op U)) (V : (Over U)ᵒᵖ)
    (r : (ORestr O U).obj V) (x : ((restrFun O U).obj G).obj V) :
    (fRestr O U f V) • r • x = r • (fRestr O U f V) • x := by
  rw [smul_smul, smul_smul]
  have hcomm : (fRestr O U f V) * r = r * (fRestr O U f V) :=
    mul_comm (G := O.obj (op V.unop.left)) _ _
  rw [hcomm]

/-- Multiplication by the restriction of a section `f ∈ O(U)` on `G|_U(V)`, as an
endomorphism of `O|_U(V)`-modules. Used to define the `O(U)`-module structure on the internal
hom. -/
noncomputable def multEndo (U : C) (f : (Oforget O).obj (op U)) (V : (Over U)ᵒᵖ) :
    ((restrFun O U).obj G).obj V ⟶ ((restrFun O U).obj G).obj V :=
  ModuleCat.homAddEquiv.symm
    { toFun := fun x => (fRestr O U f V) • x
      map_add' := fun _ _ => smul_add _ _ _
      map_smul' := fun r x => multEndo_smul_comm O G U f V r x }

/-- Multiplication by a section `f ∈ O(U)` on `G|_U` commutes with the restriction maps
of `G|_U`. -/
theorem multEndoHom_naturality (U : C) (f : (Oforget O).obj (op U))
    ⦃X Y : (Over U)ᵒᵖ⦄ (g : X ⟶ Y) :
    ((restrFun O U).obj G).map g ≫
        (ModuleCat.restrictScalars ((ORestr O U).map g).hom).map (multEndo O G U f Y) =
      multEndo O G U f X ≫ ((restrFun O U).obj G).map g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  set ρ := ((restrFun O U).obj G).map g with hρ
  change (fRestr O U f Y) • (ρ.hom x) = ρ.hom ((fRestr O U f X) • x)
  rw [map_smul]
  congr 1
  change (fRestr O U f Y) = ((ORestr O U).map g).hom (fRestr O U f X)
  rw [fRestr, fRestr]
  change ((Oforget O).map Y.unop.hom.op).hom f
      = ((Oforget O).map ((Over.forget U).map g.unop).op).hom
          (((Oforget O).map X.unop.hom.op).hom f)
  have hcomp : ((Over.forget U).map g.unop) ≫ X.unop.hom = Y.unop.hom := Over.w g.unop
  rw [← hcomp, op_comp, Functor.map_comp]
  rfl

/-- Multiplication by a section `f ∈ O(U)` on `G|_U`, as an endomorphism of the
`O|_U`-module `G|_U`. -/
noncomputable def multEndoHom (U : C) (f : (Oforget O).obj (op U)) :
    (restrFun O U).obj G ⟶ (restrFun O U).obj G where
  app V := multEndo O G U f V
  naturality g := multEndoHom_naturality O G U f g

/-- The scalar multiple of a morphism `α : F|_U ⟶ G|_U` by a section `f ∈ O(U)`: the
composite of `α` with multiplication by `f` on `G|_U`. -/
noncomputable def smulHom (U : C) (f : (Oforget O).obj (op U))
    (α : (restrFun O U).obj F ⟶ (restrFun O U).obj G) :
    (restrFun O U).obj F ⟶ (restrFun O U).obj G :=
  α ≫ multEndoHom O G U f

/-- Two morphisms of presheaves of modules which agree on every element are equal. -/
private theorem presheafOfModules_hom_ext_apply {D : Type*} [Category* D] {R : Dᵒᵖ ⥤ RingCat}
    {M N : PresheafOfModules.{t} R} {a b : M ⟶ N}
    (h : ∀ V x, (a.app V).hom x = (b.app V).hom x) : a = b :=
  PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext (h V))

/-- Scaling a morphism `F|_U ⟶ G|_U` by `1` is the identity. -/
theorem homModule_one_smul (U : C) (α : (restrFun O U).obj F ⟶ (restrFun O U).obj G) :
    smulHom O F G U 1 α = α := by
  have key : multEndoHom O G U 1 = 𝟙 _ := by
    refine presheafOfModules_hom_ext_apply fun V x => ?_
    change (fRestr O U 1 V) • x = x
    rw [fRestr, map_one, one_smul]
  rw [smulHom, key, Category.comp_id]

/-- Scaling a morphism `F|_U ⟶ G|_U` by `f * g` is scaling by `g` and then by `f`. -/
theorem homModule_mul_smul (U : C) (f g : (Oforget O).obj (op U))
    (α : (restrFun O U).obj F ⟶ (restrFun O U).obj G) :
    smulHom O F G U (f * g) α = smulHom O F G U f (smulHom O F G U g α) := by
  have keyMult : multEndoHom O G U (f * g)
      = multEndoHom O G U g ≫ multEndoHom O G U f := by
    refine presheafOfModules_hom_ext_apply fun V x => ?_
    change (fRestr O U (f * g) V) • x
        = (fRestr O U f V) • ((fRestr O U g V) • x)
    rw [fRestr, fRestr, fRestr, map_mul, mul_smul]
  rw [smulHom, smulHom, smulHom, Category.assoc, keyMult]

/-- Any scalar multiple of the zero morphism `F|_U ⟶ G|_U` is zero. -/
theorem homModule_smul_zero (U : C) (f : (Oforget O).obj (op U)) :
    smulHom O F G U f (0 : (restrFun O U).obj F ⟶ (restrFun O U).obj G) = 0 := by
  rw [smulHom, Limits.zero_comp]

/-- Scaling morphisms `F|_U ⟶ G|_U` by a section `f ∈ O(U)` is additive. -/
theorem homModule_smul_add (U : C) (f : (Oforget O).obj (op U))
    (α β : (restrFun O U).obj F ⟶ (restrFun O U).obj G) :
    smulHom O F G U f (α + β) = smulHom O F G U f α + smulHom O F G U f β := by
  rw [smulHom, smulHom, smulHom, Preadditive.add_comp]

/-- Scaling a morphism `F|_U ⟶ G|_U` is additive in the section `f ∈ O(U)`. -/
theorem homModule_add_smul (U : C) (f g : (Oforget O).obj (op U))
    (α : (restrFun O U).obj F ⟶ (restrFun O U).obj G) :
    smulHom O F G U (f + g) α = smulHom O F G U f α + smulHom O F G U g α := by
  have keyAdd : multEndoHom O G U (f + g)
      = multEndoHom O G U f + multEndoHom O G U g := by
    refine presheafOfModules_hom_ext_apply fun V x => ?_
    change (fRestr O U (f + g) V) • x
        = (fRestr O U f V) • x + (fRestr O U g V) • x
    rw [fRestr, fRestr, fRestr, map_add, add_smul]
  rw [smulHom, smulHom, smulHom, keyAdd, Preadditive.comp_add]

/-- Scaling a morphism `F|_U ⟶ G|_U` by `0` gives the zero morphism. -/
theorem homModule_zero_smul (U : C) (α : (restrFun O U).obj F ⟶ (restrFun O U).obj G) :
    smulHom O F G U 0 α = 0 := by
  have keyZero : multEndoHom O G U 0 = 0 := by
    refine presheafOfModules_hom_ext_apply fun V x => ?_
    change (fRestr O U 0 V) • x = 0
    rw [fRestr, map_zero, zero_smul]
  rw [smulHom, keyZero, Limits.comp_zero]

/-- The `O(U)`-module structure on `Hom_{O|_U}(F|_U, G|_U)`, given by pointwise addition of
morphisms and the scalar action `smulHom`. -/
@[reducible] noncomputable def homModule (U : C) :
    Module ((Oforget O).obj (op U)) ((restrFun O U).obj F ⟶ (restrFun O U).obj G) where
  smul f α := smulHom O F G U f α
  one_smul := homModule_one_smul O F G U
  mul_smul := homModule_mul_smul O F G U
  smul_zero := homModule_smul_zero O F G U
  smul_add := homModule_smul_add O F G U
  add_smul := homModule_add_smul O F G U
  zero_smul := homModule_zero_smul O F G U

/-- The value of the internal hom presheaf at `U`: `Hom_{O|_U}(F|_U, G|_U)` as an
`O(U)`-module. -/
noncomputable def internalHomObj (U : C) : ModuleCat ((Oforget O).obj (op U)) :=
  @ModuleCat.of ((Oforget O).obj (op U)) _
    ((restrFun O U).obj F ⟶ (restrFun O U).obj G) _ (homModule O F G U)

/-- The restriction map of the internal hom is additive. -/
theorem internalHomMap_map_add {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (α β : internalHomObj O F G X.unop) :
    homRestr O F G f.unop (α + β) = homRestr O F G f.unop α + homRestr O F G f.unop β := by
  have : (relocRestr O f.unop).Additive := by
    constructor
    intro M N a b
    apply PresheafOfModules.hom_ext
    intro Z
    rfl
  rw [homRestr, homRestr, homRestr, Functor.map_add, Preadditive.add_comp,
    Preadditive.comp_add]

/-- The restriction map of the internal hom is semilinear: restricting `smulHom r α` along
`f` is scaling the restriction of `α` by the restriction of `r`. -/
theorem internalHomMap_map_smul {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (r : (Oforget O).obj X) (α : (restrFun O X.unop).obj F ⟶ (restrFun O X.unop).obj G) :
    homRestr O F G f.unop (smulHom O F G X.unop r α)
      = smulHom O F G Y.unop (((Oforget O).map f).hom r) (homRestr O F G f.unop α) := by
  have hsplit : ∀ (β : (restrFun O X.unop).obj F ⟶ (restrFun O X.unop).obj G)
      (γ : (restrFun O X.unop).obj G ⟶ (restrFun O X.unop).obj G),
      homRestr O F G f.unop (β ≫ γ)
        = homRestr O F G f.unop β ≫ homRestr O G G f.unop γ := by
    intro β γ
    rw [homRestr, homRestr, homRestr, Functor.map_comp]
    simp only [Category.assoc, eqToHom_refl, Category.id_comp]
  have keyScalar : ∀ (W : (Over Y.unop)ᵒᵖ),
      fRestr O Y.unop (((Oforget O).map f).hom r) W
        = fRestr O X.unop r ((Over.map f.unop).op.obj W) := by
    intro W
    rw [fRestr, fRestr]
    change ((Oforget O).map W.unop.hom.op).hom (((Oforget O).map f).hom r)
        = ((Oforget O).map ((Over.map f.unop).obj W.unop).hom.op).hom r
    have hcomp : ((Over.map f.unop).obj W.unop).hom = W.unop.hom ≫ f.unop := rfl
    rw [hcomp, op_comp, Functor.map_comp]
    rfl
  have keyMult : homRestr O G G f.unop (multEndoHom O G X.unop r)
      = multEndoHom O G Y.unop (((Oforget O).map f).hom r) := by
    refine presheafOfModules_hom_ext_apply fun W x => ?_
    rw [homRestr]
    change (fRestr O X.unop r ((Over.map f.unop).op.obj W)) • x
        = (fRestr O Y.unop (((Oforget O).map f).hom r) W) • x
    rw [keyScalar]
  rw [smulHom, smulHom, hsplit, keyMult]

/-- The restriction map of the internal hom presheaf for a morphism `f : X ⟶ Y` of `Cᵒᵖ`:
the `O`-semilinear map given by `homRestr`. -/
noncomputable def internalHomMap {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    internalHomObj O F G X.unop ⟶
      (ModuleCat.restrictScalars ((Oforget O).map f).hom).obj (internalHomObj O F G Y.unop) :=
  ModuleCat.homAddEquiv.symm
    { toFun := fun α => homRestr O F G f.unop α
      map_add' := fun α β => internalHomMap_map_add O F G f α β
      map_smul' := fun r α => internalHomMap_map_smul O F G f r α }

/-- The restriction map of the internal hom along the identity is the identity. -/
theorem internalHom_map_id (X : Cᵒᵖ) :
    internalHomMap O F G (𝟙 X) =
      𝟙 (internalHomObj O F G X.unop) ≫
        (ModuleCat.restrictScalarsId' ((Oforget O).map (𝟙 X)).hom
          (by rw [(Oforget O).map_id]; rfl)).inv.app (internalHomObj O F G X.unop) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  change homRestr O F G (𝟙 X).unop α = α
  rw [unop_id]
  apply (PresheafOfModules.toPresheaf (ORestr O X.unop)).map_injective
  change (presheafHom F.presheaf G.presheaf).map (𝟙 X.unop).op
        ((PresheafOfModules.toPresheaf (ORestr O X.unop)).map α)
      = (PresheafOfModules.toPresheaf (ORestr O X.unop)).map α
  rw [op_id]
  simp

/-- Restriction along `g ≫ f` is restriction along `f` followed by restriction along `g`.
Proved by passing to the underlying abelian hom-presheaf `presheafHom`, where it is plain
functoriality. -/
theorem homRestr_comp {W V U : C} (g : W ⟶ V) (f : V ⟶ U)
    (α : (restrFun O U).obj F ⟶ (restrFun O U).obj G) :
    homRestr O F G (g ≫ f) α = homRestr O F G g (homRestr O F G f α) := by
  apply (PresheafOfModules.toPresheaf (ORestr O W)).map_injective
  change (presheafHom F.presheaf G.presheaf).map (g ≫ f).op
        ((PresheafOfModules.toPresheaf (ORestr O U)).map α)
      = (presheafHom F.presheaf G.presheaf).map g.op
          ((presheafHom F.presheaf G.presheaf).map f.op
            ((PresheafOfModules.toPresheaf (ORestr O U)).map α))
  rw [op_comp, Functor.map_comp_apply]

/-- The restriction maps of the internal hom are compatible with composition. -/
theorem internalHom_map_comp {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    internalHomMap O F G (f ≫ g) =
      internalHomMap O F G f ≫
        (ModuleCat.restrictScalars ((Oforget O).map f).hom).map (internalHomMap O F G g) ≫
          (ModuleCat.restrictScalarsComp' ((Oforget O).map f).hom ((Oforget O).map g).hom
            ((Oforget O).map (f ≫ g)).hom (by rw [(Oforget O).map_comp]; rfl)).inv.app
              (internalHomObj O F G Z.unop) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  change homRestr O F G (f ≫ g).unop α = homRestr O F G g.unop (homRestr O F G f.unop α)
  rw [unop_comp]
  exact homRestr_comp O F G g.unop f.unop α

/-- The internal hom presheaf `𝓗om_O(F, G)`: the presheaf of `O`-modules whose value at `U` is
`Hom_{O|_U}(F|_U, G|_U)`, with restriction maps `homRestr` and the `O(U)`-module structure
`homModule`. -/
noncomputable def internalHom : PresheafOfModules (Oforget O) where
  obj X := internalHomObj O F G X.unop
  map f := internalHomMap O F G f
  map_id X := internalHom_map_id O F G X
  map_comp f g := internalHom_map_comp O F G f g

variable {J : GrothendieckTopology C}

variable {U : C} (S : J.Cover U)

/-- A family of local morphisms `φ I : F|_{I.Y} ⟶ G|_{I.Y}`, indexed by the arrows
`I.f : I.Y ⟶ U` of a cover `S` of `U`, is *compatible* when its members agree after
being restricted to the overlaps `I₁.Y ×_U I₂.Y` (the relations of the cover). -/
def IsCompatibleFamily
    (φ : ∀ I : S.Arrow, (restrFun O I.Y).obj F ⟶ (restrFun O I.Y).obj G) : Prop :=
  ∀ ⦃I₁ I₂ : S.Arrow⦄ (r : I₁.Relation I₂),
    homRestr O F G r.g₁ (φ I₁) = homRestr O F G r.g₂ (φ I₂)

/-- The restrictions `(α|_{I.Y})_I` of a morphism `α : F|_U ⟶ G|_U` to the members of a cover
`S` form a compatible family. -/
theorem restrictToCover_isCompatible
    (α : (restrFun O U).obj F ⟶ (restrFun O U).obj G) :
    IsCompatibleFamily O F G S (fun I => homRestr O F G I.f α) := by
  intro I₁ I₂ r
  rw [← homRestr_comp, ← homRestr_comp, r.w]

/-- The map sending a morphism `α : F|_U ⟶ G|_U` to the compatible family `(α|_{I.Y})_I` of its
restrictions to the members of the cover `S`. -/
noncomputable def restrictToCover
    (α : (restrFun O U).obj F ⟶ (restrFun O U).obj G) :
    { φ : ∀ I : S.Arrow, (restrFun O I.Y).obj F ⟶ (restrFun O I.Y).obj G //
        IsCompatibleFamily O F G S φ } :=
  ⟨fun I => homRestr O F G I.f α, restrictToCover_isCompatible O F G S α⟩

/-- The underlying `Ab`-presheaf section of a morphism `β : F|_V ⟶ G|_V`, as an element of
`(presheafHom F.presheaf G.presheaf).obj (op V)`. -/
noncomputable def toUnderlying {V : C} (β : (restrFun O V).obj F ⟶ (restrFun O V).obj G) :
    (presheafHom F.presheaf G.presheaf).obj (op V) :=
  (PresheafOfModules.toPresheaf (ORestr O V)).map β

/-- Restricting a section of the abelian hom-presheaf along `g` corresponds to `homRestr`. -/
theorem toUnderlying_restr {V W : C} (g : W ⟶ V)
    (β : (restrFun O V).obj F ⟶ (restrFun O V).obj G) :
    (presheafHom F.presheaf G.presheaf).map g.op (toUnderlying O F G β)
      = toUnderlying O F G (homRestr O F G g β) := rfl

/-- The sections `toUnderlying (φ I)` of a compatible family of morphisms over the members of
`S` form a compatible family of elements of the hom-presheaf, which is what its sheaf condition
asks for. -/
theorem toUnderlying_isCompatible
    (φ : ∀ I : S.Arrow, (restrFun O I.Y).obj F ⟶ (restrFun O I.Y).obj G)
    (hφ : IsCompatibleFamily O F G S φ) :
    Presieve.FamilyOfElements.Compatible
      (fun Y f hf ↦ toUnderlying O F G (φ ⟨Y, f, hf⟩) :
        Presieve.FamilyOfElements (presheafHom F.presheaf G.presheaf) (S : Sieve U).arrows) := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hcomm
  change (presheafHom F.presheaf G.presheaf).map g₁.op (toUnderlying O F G (φ ⟨Y₁, f₁, hf₁⟩))
     = (presheafHom F.presheaf G.presheaf).map g₂.op (toUnderlying O F G (φ ⟨Y₂, f₂, hf₂⟩))
  rw [toUnderlying_restr, toUnderlying_restr]
  exact congrArg (toUnderlying O F G) (hφ (I₁ := ⟨Y₁, f₁, hf₁⟩) (I₂ := ⟨Y₂, f₂, hf₂⟩)
    (GrothendieckTopology.Cover.Arrow.Relation.mk Z g₁ g₂ hcomm))

/-- The amalgamation, over the cover `S`, of the underlying abelian sections of a compatible
family `φ`, valued in the hom-presheaf `presheafHom F.presheaf G.presheaf` (a sheaf since `G`
is a sheaf). -/
noncomputable def gluedUnder
    (hG : Presheaf.IsSheaf J G.presheaf)
    (φ : ∀ I : S.Arrow, (restrFun O I.Y).obj F ⟶ (restrFun O I.Y).obj G)
    (hφ : IsCompatibleFamily O F G S φ) :
    (presheafHom F.presheaf G.presheaf).obj (op U) :=
  let hPH : Presheaf.IsSheaf J (presheafHom F.presheaf G.presheaf) :=
    Presheaf.IsSheaf.hom F.presheaf G.presheaf hG
  let fam : Presieve.FamilyOfElements (presheafHom F.presheaf G.presheaf) (S : Sieve U).arrows :=
    fun Y f hf => toUnderlying O F G (φ ⟨Y, f, hf⟩)
  (hPH.isSheafFor _ S.2).amalgamate fam (toUnderlying_isCompatible O F G S φ hφ)

/-- The amalgamation `gluedUnder` restricts to `toUnderlying (φ I)` on each member `I` of the
cover. -/
theorem gluedUnder_restr
    (hG : Presheaf.IsSheaf J G.presheaf)
    (φ : ∀ I : S.Arrow, (restrFun O I.Y).obj F ⟶ (restrFun O I.Y).obj G)
    (hφ : IsCompatibleFamily O F G S φ) (I : S.Arrow) :
    (presheafHom F.presheaf G.presheaf).map I.f.op (gluedUnder O F G S hG φ hφ)
      = toUnderlying O F G (φ I) :=
  ((Presheaf.IsSheaf.hom F.presheaf G.presheaf hG).isSheafFor _ S.2).valid_glue
    (x := fun Y f hf => toUnderlying O F G (φ ⟨Y, f, hf⟩))
    (toUnderlying_isCompatible O F G S φ hφ) I.f I.hf

/-- If `g : Z ⟶ W₀` lies in the sieve on `W₀` obtained by pulling `Sx` back along `W₀.hom`,
then the structure map `Z.hom` lies in `Sx`. -/
theorem mem_of_overEquiv (Sx : J.Cover U) (W₀ : Over U) {Z : Over U} (g : Z ⟶ W₀)
    (hg : ((Sieve.overEquiv W₀).symm ((Sx : Sieve U).pullback W₀.hom)).arrows g) :
    (Sx : Sieve U).arrows Z.hom := by
  rw [Sieve.overEquiv_symm_iff, Sieve.pullback_apply] at hg
  rwa [Over.w g] at hg

/-- The `O|_U`-linear morphism `F|_U ⟶ G|_U` glued from a compatible family `φ`, whose
underlying abelian section is `gluedUnder`. Its `O|_U`-linearity is checked via the separation
half of the sheaf condition on `G|_U` and the linearity of the members of the family. -/
noncomputable def gluedHom
    (hG : Presheaf.IsSheaf J G.presheaf)
    (φ : ∀ I : S.Arrow, (restrFun O I.Y).obj F ⟶ (restrFun O I.Y).obj G)
    (hφ : IsCompatibleFamily O F G S φ) :
    (restrFun O U).obj F ⟶ (restrFun O U).obj G :=
  PresheafOfModules.homMk (gluedUnder O F G S hG φ hφ) (by
    intro X r m
    set ᾱ := gluedUnder O F G S hG φ hφ with hbar
    have hGslice : Presheaf.IsSheaf (J.over U) (((restrFun O U).obj G).presheaf) :=
      (Over.forget U).op_comp_isSheaf_of_isSheaf (J.over U) J G.presheaf hG
    obtain ⟨W₀⟩ := X
    let T : (J.over U).Cover W₀ :=
      ⟨(Sieve.overEquiv W₀).symm ((S : Sieve U).pullback W₀.hom), by
        rw [GrothendieckTopology.mem_over_iff, OrderIso.apply_symm_apply]
        exact J.pullback_stable W₀.hom S.2⟩
    refine hGslice.isSeparated W₀ T.1 T.2 _ _ ?_
    intro Z g hg
    have hZmem : (S : Sieve U).arrows Z.hom := mem_of_overEquiv S W₀ g hg
    erw [PresheafOfModules.map_smul ((restrFun O U).obj G) g.op r
          (ConcreteCategory.hom (ᾱ.app (op W₀)) m),
        ← NatTrans.naturality_apply ᾱ g.op (r • m),
        ← NatTrans.naturality_apply ᾱ g.op m,
        PresheafOfModules.map_smul ((restrFun O U).obj F) g.op r m]
    set I : S.Arrow := ⟨Z.left, Z.hom, hZmem⟩ with hI
    have hrestr := gluedUnder_restr O F G S hG φ hφ I
    have hmapapp := presheafHom_map_app (F := F.presheaf) (G := G.presheaf)
      (𝟙 Z.left) I.f Z.hom (Category.id_comp Z.hom) ᾱ
    have key : ᾱ.app (op (Over.mk Z.hom))
        = (toUnderlying O F G (φ I)).app (op (Over.mk (𝟙 Z.left))) := by
      rw [← hmapapp, hrestr]
    have keyZ : ᾱ.app (op Z)
        = (toUnderlying O F G (φ I)).app (op (Over.mk (𝟙 Z.left))) := key
    rw [keyZ]
    exact ((φ I).app (op (Over.mk (𝟙 Z.left)))).hom.map_smul _ _)

/-- The glued morphism `gluedHom` restricts to `φ I` on every member `I` of the cover. -/
theorem homRestr_gluedHom
    (hG : Presheaf.IsSheaf J G.presheaf)
    (φ : ∀ I : S.Arrow, (restrFun O I.Y).obj F ⟶ (restrFun O I.Y).obj G)
    (hφ : IsCompatibleFamily O F G S φ) (I : S.Arrow) :
    homRestr O F G I.f (gluedHom O F G S hG φ hφ) = φ I := by
  apply (PresheafOfModules.toPresheaf (ORestr O I.Y)).map_injective
  change toUnderlying O F G (homRestr O F G I.f (gluedHom O F G S hG φ hφ))
    = toUnderlying O F G (φ I)
  rw [← toUnderlying_restr]
  exact gluedUnder_restr O F G S hG φ hφ I

/-- If `G` is a sheaf, a morphism `F|_U ⟶ G|_U` of `O|_U`-modules is determined by its
restrictions to the members of a cover `S` of `U`.

This is the separation half of the sheaf condition on `G|_U`: the sheaf `G` relocalizes to a
sheaf `(Over.forget U).op ⋙ G.presheaf` for the slice topology `J.over U`, two morphisms agreeing
on the members of `S` agree at every slice object whose structure map lies in `S`, and the cover
`S` pulled back along the structure map of an object `W` of `Over U` is a cover of `W` for
`J.over U`, on which `Presheaf.IsSheaf.hom_ext` applies. -/
theorem internalHom_glue_injective
    (hG : Presheaf.IsSheaf J G.presheaf) :
    Function.Injective (restrictToCover O F G S) := by
  intro a a' haa
  rw [restrictToCover, restrictToCover, Subtype.mk_eq_mk, funext_iff] at haa
  have hGslice : Presheaf.IsSheaf (J.over U) ((Over.forget U).op ⋙ G.presheaf) :=
    (Over.forget U).op_comp_isSheaf_of_isSheaf (J.over U) J G.presheaf hG
  have homRestr_app :
      ∀ {V : C} (g : V ⟶ U)
        (hgg : homRestr O F G g a = homRestr O F G g a') (W : (Over V)ᵒᵖ),
        a.app ((Over.map g).op.obj W) = a'.app ((Over.map g).op.obj W) := by
    intro V g hgg W
    have h3 : (relocRestr O g).map a = (relocRestr O g).map a' := by
      have key : ∀ b : (restrFun O U).obj F ⟶ (restrFun O U).obj G,
          (relocRestr O g).map b
            = eqToHom (reloc_restr_obj O F g) ≫ homRestr O F G g b
                ≫ eqToHom (reloc_restr_obj O G g).symm := by
        intro b
        rw [homRestr, ← Category.assoc, ← Category.assoc, eqToHom_trans, eqToHom_refl,
          Category.id_comp, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
      rw [key a, key a', hgg]
    exact congrArg (fun m => PresheafOfModules.Hom.app m W) h3
  have keyApp : ∀ (P : Over U), (S : Sieve U).arrows P.hom →
      a.app (op P) = a'.app (op P) := by
    intro P hP
    have happ := homRestr_app P.hom (haa ⟨P.left, P.hom, hP⟩) (op (Over.mk (𝟙 P.left)))
    have hPeq : Over.mk (𝟙 P.left ≫ P.hom) = P := by
      rw [Category.id_comp]
      rfl
    rw [← hPeq]
    exact happ
  apply PresheafOfModules.hom_ext
  intro W
  apply (forget₂ (ModuleCat ((ORestr O U).obj W)) Ab).map_injective
  set e₁ := (PresheafOfModules.toPresheaf (ORestr O U)).map a with he₁
  set e₂ := (PresheafOfModules.toPresheaf (ORestr O U)).map a' with he₂
  change e₁.app W = e₂.app W
  have keyApp' : ∀ (P : Over U), (S : Sieve U).arrows P.hom →
      e₁.app (op P) = e₂.app (op P) := by
    intro P hP
    exact congrArg (forget₂ (ModuleCat ((ORestr O U).obj (op P))) Ab).map (keyApp P hP)
  have hT : (Sieve.overEquiv W.unop).symm ((S.pullback W.unop.hom) : Sieve W.unop.left)
      ∈ (J.over U) W.unop := by
    rw [J.mem_over_iff, OrderIso.apply_symm_apply]
    exact (S.pullback W.unop.hom).2
  set T : (J.over U).Cover W.unop :=
    ⟨(Sieve.overEquiv W.unop).symm ((S.pullback W.unop.hom) : Sieve W.unop.left), hT⟩ with hTdef
  have hfin := hGslice.hom_ext T (e₁.app W) (e₂.app W) ?_
  · convert hfin
  · intro I'
    have hmem : (S : Sieve U).arrows I'.Y.hom := mem_of_overEquiv S W.unop I'.f I'.hf
    have hnat₁ := e₁.naturality I'.f.op
    have hnat₂ := e₂.naturality I'.f.op
    change e₁.app W ≫ ((PresheafOfModules.toPresheaf (ORestr O U)).obj
        ((restrFun O U).obj G)).map I'.f.op
      = e₂.app W ≫ ((PresheafOfModules.toPresheaf (ORestr O U)).obj
        ((restrFun O U).obj G)).map I'.f.op
    rw [← hnat₁, ← hnat₂, keyApp' I'.Y hmem]

/-- If `G` is a sheaf, every compatible family `(φ I)_I` of morphisms `F|_{I.Y} ⟶ G|_{I.Y}`
over the members of a cover `S` of `U` is the family of restrictions of a morphism
`F|_U ⟶ G|_U`.

This is the gluing half of the sheaf condition: the underlying sections of the family glue in
the sheaf of homs `presheafHom F.presheaf G.presheaf` to `gluedUnder`, which is upgraded to an
`O|_U`-linear morphism `gluedHom` restricting to each member of the family. -/
theorem internalHom_glue_surjective
    (hG : Presheaf.IsSheaf J G.presheaf) :
    Function.Surjective (restrictToCover O F G S) := by
  rintro ⟨φ, hφ⟩
  refine ⟨gluedHom O F G S hG φ hφ, ?_⟩
  rw [restrictToCover, Subtype.mk_eq_mk]
  funext I
  exact homRestr_gluedHom O F G S hG φ hφ I

/-- If `G` is a sheaf, then for every cover `S` of `U`, restricting a morphism
`F|_U ⟶ G|_U` to the members of `S` is a bijection onto the set of compatible families of
local morphisms. It is assembled from the uniqueness half `internalHom_glue_injective` and the
existence half `internalHom_glue_surjective`. -/
theorem internalHom_glue
    (hG : Presheaf.IsSheaf J G.presheaf) :
    Function.Bijective (restrictToCover O F G S) :=
  ⟨internalHom_glue_injective O F G S hG, internalHom_glue_surjective O F G S hG⟩

set_option maxHeartbeats 2000000 in
-- this proof's elaboration needs more than the default heartbeat budget
/-- Let `O` be a presheaf of commutative rings on a site `C`, let `F` be a presheaf of
`O`-modules and let `G` be a sheaf of `O`-modules. Then the internal hom presheaf
`𝓗om_O(F, G) = internalHom O F G` is a sheaf of `O`-modules, i.e. its underlying abelian
presheaf is a sheaf. -/
theorem internalHom_isSheaf
    (hG : Presheaf.IsSheaf J G.presheaf) :
    Presheaf.IsSheaf J (internalHom O F G).presheaf := by
  rw [Presheaf.isSheaf_iff_multifork]
  intro X S
  have hbij := internalHom_glue O F G S hG
  have hι : ∀ (I : S.Arrow), (S.multifork (internalHom O F G).presheaf).ι I
      = (internalHom O F G).presheaf.map I.f.op := fun I => by
    simp [GrothendieckTopology.Cover.multifork]
  set glueEquiv := Equiv.ofBijective (restrictToCover O F G S) hbij with hge
  have hsymm : ∀ (φ : ∀ I : S.Arrow, (restrFun O I.Y).obj F ⟶ (restrFun O I.Y).obj G)
      (h : IsCompatibleFamily O F G S φ) (I : S.Arrow),
      homRestr O F G I.f (glueEquiv.symm ⟨φ, h⟩) = φ I := by
    intro φ h I
    have heq := glueEquiv.apply_symm_apply ⟨φ, h⟩
    rw [hge, Equiv.ofBijective_apply, restrictToCover] at heq
    exact congrFun (congrArg Subtype.val heq) I
  have hcompat : ∀ (E : Limits.Multifork (S.index (internalHom O F G).presheaf))
      (e : E.pt),
      IsCompatibleFamily O F G S
        (fun I => (ConcreteCategory.hom (E.ι I)) e) := by
    intro E e I₁ I₂ r
    have hc := congrArg (fun (m : E.pt ⟶ _) => (ConcreteCategory.hom m) e)
      (E.condition (GrothendieckTopology.Cover.Relation.mk (S := S) r))
    simp only [GrothendieckTopology.Cover.index_fst, GrothendieckTopology.Cover.index_snd,
      ConcreteCategory.comp_apply] at hc
    exact hc
  set L : ∀ (E : Limits.Multifork (S.index (internalHom O F G).presheaf)),
      E.pt → ((internalHom O F G).presheaf.obj (op X)) :=
    fun E e => glueEquiv.symm ⟨fun I => (ConcreteCategory.hom (E.ι I)) e, hcompat E e⟩ with hL
  have hLrestr : ∀ (E : Limits.Multifork (S.index (internalHom O F G).presheaf))
      (e : E.pt) (I : S.Arrow),
      homRestr O F G I.f (L E e) = (ConcreteCategory.hom (E.ι I)) e := fun E e I =>
    hsymm _ (hcompat E e) I
  have hadd : ∀ (I : S.Arrow) (x y : (internalHom O F G).presheaf.obj (op X)),
      homRestr O F G I.f (x + y) = homRestr O F G I.f x + homRestr O F G I.f y :=
    fun I x y => internalHomMap_map_add O F G I.f.op x y
  have hz : ∀ (I : S.Arrow),
      homRestr O F G I.f (0 : (internalHom O F G).presheaf.obj (op X)) = 0 := by
    intro I
    have h := hadd I 0 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  have hext : ∀ x y : (internalHom O F G).presheaf.obj (op X),
      (∀ I : S.Arrow, homRestr O F G I.f x = homRestr O F G I.f y) → x = y :=
    fun x y h => hbij.injective (Subtype.ext (funext h))
  refine ⟨Limits.Multifork.IsLimit.mk _ (fun E => ?_) (fun E i => ?_) (fun E m hm => ?_)⟩
  · refine AddCommGrpCat.ofHom
      { toFun := L E
        map_zero' := ?_
        map_add' := ?_ }
    · refine hext _ _ fun I => ?_
      rw [hLrestr, map_zero, hz I]
    · intro a b
      refine hext _ _ fun I => ?_
      rw [hLrestr, map_add, ← hLrestr E a I, ← hLrestr E b I, hadd I (L E a) (L E b)]
  · apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro e
    change (ConcreteCategory.hom ((S.multifork (internalHom O F G).presheaf).ι i))
        (L E e) = (ConcreteCategory.hom (E.ι i)) e
    rw [hι i]
    exact hLrestr E e i
  · apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro e
    change (ConcreteCategory.hom m) e = L E e
    refine hext _ _ fun I => ?_
    rw [hLrestr]
    have h2 := congrArg (fun (k : E.pt ⟶ _) => (ConcreteCategory.hom k) e) (hm I)
    simp only [ConcreteCategory.comp_apply] at h2
    rw [hι I] at h2
    exact h2

end MathlibExt.AlgebraicGeometry.ModuleInternalHom
