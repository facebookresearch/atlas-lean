/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex

module

public import MathlibExt.CategoryTheory.Monoidal.Mod.Closed

/-!
# Original free-module internal-Hom evaluation

The original free unit and parameterized free extension identify the unchanged
module internal-Hom equalizer with its ambient internal Hom. The same maps
retain the original auxiliary scalar action, both inverse laws, whole target
naturality and the full balanced source precomposition formula.

The auxiliary module and its action are the original provider from
`Mod.InternalHom`; no second auxiliary module is constructed here.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.Mod.FreeInternalHom
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] [HasEqualizers C] (A : CommMon C)

/-- The original free-adjunction generator has its actual original free module as target. -/
abbrev generator (P : C) : P ⟶ A.X ⊗ P :=
  (Mod.freeForgetAdjunction A.X).unit.app P

omit [MonoidalClosed C] [HasEqualizers C] in
/-- The original free generator retains its literal unit insertion and coefficient unitor. -/
private theorem generator_eq (P : C) : generator A P = (λ_ P).inv ≫ ((η : 𝟙_ C ⟶ A.X) ▷ P) := by
  have h := Mod.freeForgetAdjunction_unit_app A.X P
  change generator A P = (λ_ P).inv ≫ ((η : 𝟙_ C ⟶ A.X) ▷ P) ≫ 𝟙 _ at h
  simpa only [Category.comp_id] using h

omit [MonoidalClosed C] [HasEqualizers C] in
/-- The whole original free action after its generator is the original full carrier identity. -/
private theorem generator_action (P : C) :
    (A.X ◁ generator A P) ≫ ((Mod.free A.X).obj P).mod.smul = 𝟙 _ := by
  change (A.X ◁ generator A P) ≫
    ((α_ A.X A.X P).inv ≫ ((μ : A.X ⊗ A.X ⟶ A.X) ▷ P)) = 𝟙 _
  rw [generator_eq, whiskerLeft_comp, Category.assoc,
    associator_inv_naturality_middle_assoc]
  rw [← comp_whiskerRight, MonObj.mul_one]
  monoidal

/-- The original parameterized free extension retains the actual associator, coefficient map and
target module action. -/
def parameterExtension (P T : C) (N : Mod C A.X) (q : P ⊗ T ⟶ N.X) :
    (A.X ⊗ P) ⊗ T ⟶ N.X :=
  (α_ A.X P T).hom ≫ (A.X ◁ q) ≫ N.mod.smul

omit [MonoidalClosed C] [HasEqualizers C] in
/-- The same entire parameterized extension is the original chosen free-adjunction extension after
the actual coefficient associator. -/
private theorem parameterExtension_original (P T : C) (N : Mod C A.X) (q : P ⊗ T ⟶ N.X) :
    parameterExtension A P T N q =
      (α_ A.X P T).hom ≫
        (((Mod.freeForgetAdjunction A.X).homEquiv (P ⊗ T) N).symm q).hom := by
  rw [Mod.freeForgetAdjunction_homEquiv_symm_apply_hom]
  change (α_ A.X P T).hom ≫ (A.X ◁ q) ≫ N.mod.smul =
    (α_ A.X P T).hom ≫ 𝟙 (A.X ⊗ (P ⊗ T)) ≫ (A.X ◁ q) ≫ N.mod.smul
  rw [Category.id_comp]

omit [MonoidalClosed C] [HasEqualizers C] in
/-- The actual coefficient associator is linear for the two unchanged original free actions. -/
private theorem free_associator_linear (P T : C) :
    (((Mod.free A.X).obj P).mod.smul ▷ T) ≫ (α_ A.X P T).hom =
      (α_ A.X ((Mod.free A.X).obj P).X T).hom ≫
        (A.X ◁ (α_ A.X P T).hom) ≫ ((Mod.free A.X).obj (P ⊗ T)).mod.smul := by
  have h : ((α_ A.X A.X P).inv ▷ T) ≫ (α_ (A.X ⊗ A.X) P T).hom =
      (α_ A.X (A.X ⊗ P) T).hom ≫ (A.X ◁ (α_ A.X P T).hom) ≫
        (α_ A.X A.X (P ⊗ T)).inv := by monoidal
  change (((α_ A.X A.X P).inv ≫ ((μ : A.X ⊗ A.X ⟶ A.X) ▷ P)) ▷ T) ≫
      (α_ A.X P T).hom =
    (α_ A.X (A.X ⊗ P) T).hom ≫ (A.X ◁ (α_ A.X P T).hom) ≫
      (α_ A.X A.X (P ⊗ T)).inv ≫ ((μ : A.X ⊗ A.X ⟶ A.X) ▷ (P ⊗ T))
  rw [comp_whiskerRight, Category.assoc]
  rw [associator_naturality_left]
  simpa only [Category.assoc] using
    congrArg (fun f => f ≫ ((μ : A.X ⊗ A.X ⟶ A.X) ▷ (P ⊗ T))) h

omit [MonoidalClosed C] [HasEqualizers C] in
/-- The complete original parameterized extension is linear on the whole free source, before any
unit or coefficient point is chosen. -/
theorem parameterExtension_linear (P T : C) (N : Mod C A.X) (q : P ⊗ T ⟶ N.X) :
    (((Mod.free A.X).obj P).mod.smul ▷ T) ≫ parameterExtension A P T N q =
      (α_ A.X ((Mod.free A.X).obj P).X T).hom ≫
        (A.X ◁ parameterExtension A P T N q) ≫ N.mod.smul := by
  let f : (Mod.free A.X).obj (P ⊗ T) ⟶ N :=
    ((Mod.freeForgetAdjunction A.X).homEquiv (P ⊗ T) N).symm q
  let j : A.X ⊗ (P ⊗ T) ⟶ N.X := f.hom
  let p : A.X ⊗ (A.X ⊗ P) ⟶ A.X ⊗ P := ((Mod.free A.X).obj P).mod.smul
  let p' : A.X ⊗ (A.X ⊗ (P ⊗ T)) ⟶ A.X ⊗ (P ⊗ T) :=
    ((Mod.free A.X).obj (P ⊗ T)).mod.smul
  have hf : p' ≫ j = (A.X ◁ j) ≫ N.mod.smul := f.isModHom.smul_hom
  rw [parameterExtension_original]
  change (p ▷ T) ≫
      ((α_ A.X P T).hom ≫ j) =
    (α_ A.X (A.X ⊗ P) T).hom ≫
      (A.X ◁ ((α_ A.X P T).hom ≫ j)) ≫ N.mod.smul
  have hp : (p ▷ T) ≫ (α_ A.X P T).hom =
      (α_ A.X (A.X ⊗ P) T).hom ≫ (A.X ◁ (α_ A.X P T).hom) ≫ p' :=
    free_associator_linear A P T
  rw [← Category.assoc, hp]
  simp only [Category.assoc, hf, whiskerLeft_comp]

omit [MonoidalClosed C] [HasEqualizers C] in
/-- The same original unit insertion commutes with the actual coefficient associator on the entire
free carrier. -/
theorem generator_tensor (P T : C) :
    (generator A P ▷ T) ≫ (α_ A.X P T).hom = generator A (P ⊗ T) := by
  rw [generator_eq, generator_eq, comp_whiskerRight, Category.assoc,
    associator_naturality_left]
  have h : ((λ_ P).inv ▷ T) ≫ (α_ (𝟙_ C) P T).hom = (λ_ (P ⊗ T)).inv := by
    monoidal
  simpa only [Category.assoc] using
    congrArg (fun f => f ≫ ((η : 𝟙_ C ⟶ A.X) ▷ (P ⊗ T))) h

omit [MonoidalClosed C] [HasEqualizers C] in
/-- Every whole parameterized original free extension recovers its unchanged coefficient map after
the actual free generator. -/
theorem parameterExtension_generator (P T : C) (N : Mod C A.X) (q : P ⊗ T ⟶ N.X) :
    (generator A P ▷ T) ≫ parameterExtension A P T N q = q := by
  let f : (Mod.free A.X).obj (P ⊗ T) ⟶ N :=
    ((Mod.freeForgetAdjunction A.X).homEquiv (P ⊗ T) N).symm q
  let j : A.X ⊗ (P ⊗ T) ⟶ N.X := f.hom
  have hf : generator A (P ⊗ T) ≫ j = q :=
    ((Mod.freeForgetAdjunction A.X).homEquiv_unit (P ⊗ T) N f).symm.trans
      (Equiv.apply_symm_apply _ q)
  rw [parameterExtension_original]
  change (generator A P ▷ T) ≫ ((α_ A.X P T).hom ≫ j) = q
  rw [← Category.assoc, generator_tensor]
  exact hf

omit [HasEqualizers C] in
/-- Original parameterized free extension satisfies the actual module internal-Hom equalizer pair
on the whole source. -/
theorem parameterExtension_condition (P T : C) (N : Mod C A.X) (q : P ⊗ T ⟶ N.X) :
    MonoidalClosed.curry (parameterExtension A P T N q) ≫
        Mod.internalHomPre A ((Mod.free A.X).obj P) N =
      MonoidalClosed.curry (parameterExtension A P T N q) ≫
        Mod.internalHomPost A ((Mod.free A.X).obj P) N := by
  let F := (Mod.free A.X).obj P
  let E := (ihom F.X).obj N.X
  let p : F.X ⊗ T ⟶ N.X := parameterExtension A P T N q
  change MonoidalClosed.curry p ≫ (MonoidalClosed.pre F.mod.smul).app N.X =
    MonoidalClosed.curry p ≫ MonoidalClosed.curry
      ((α_ A.X F.X E).hom ≫ (A.X ◁ (ihom.ev F.X).app N.X) ≫ N.mod.smul)
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_curry,
    MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
  change (F.mod.smul ▷ T) ≫ p =
    ((A.X ⊗ F.X) ◁ MonoidalClosed.curry p) ≫
      (α_ A.X F.X E).hom ≫ (A.X ◁ (ihom.ev F.X).app N.X) ≫ N.mod.smul
  rw [associator_naturality_right_assoc, ← whiskerLeft_comp_assoc,
    MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
  exact parameterExtension_linear A P T N q

/-- Actual free-module internal-Hom evaluation uses the existing equalizer inclusion and the
original entire free unit. -/
def forward (P : C) (N : Mod C A.X) :
    ((Mod.internalHomOfEqualizer A ((Mod.free A.X).obj P)).obj N).X ⟶ (ihom P).obj N.X :=
  Mod.internalHomι A ((Mod.free A.X).obj P) N ≫
    (MonoidalClosed.pre (generator A P)).app N.X

/-- The inverse is the lift into the original selected module internal-Hom equalizer of genuine
full free extension. -/
def inverse (P : C) (N : Mod C A.X) :
    (ihom P).obj N.X ⟶ ((Mod.internalHomOfEqualizer A ((Mod.free A.X).obj P)).obj N).X :=
  Fork.IsLimit.lift (Mod.internalHomIsLimit A ((Mod.free A.X).obj P) N)
    (MonoidalClosed.curry
      (parameterExtension A P ((ihom P).obj N.X) N ((ihom.ev P).app N.X)))
    (parameterExtension_condition A P ((ihom P).obj N.X) N ((ihom.ev P).app N.X))

/-- The complete original equalizer projection retains the actual parameterized free-extension
transpose. -/
@[reassoc]
theorem inverse_ι (P : C) (N : Mod C A.X) :
    inverse A P N ≫ Mod.internalHomι A ((Mod.free A.X).obj P) N =
      MonoidalClosed.curry
        (parameterExtension A P ((ihom P).obj N.X) N ((ihom.ev P).app N.X)) :=
  Fork.IsLimit.lift_ι' _ _ _

omit [MonoidalClosed C] [HasEqualizers C] in
/-- The actual parameterized free extension retains every whole parameter map before the original
coefficient arrow. -/
theorem parameterExtension_precompose (P : C) {T T' : C} (f : T' ⟶ T)
    (N : Mod C A.X) (q : P ⊗ T ⟶ N.X) :
    ((A.X ⊗ P) ◁ f) ≫ parameterExtension A P T N q =
      parameterExtension A P T' N ((P ◁ f) ≫ q) := by
  simp only [parameterExtension, whiskerLeft_comp]
  rw [associator_naturality_right_assoc]
  simp only [Category.assoc]

/-- The original module end relation reconstructs the complete free-source evaluation from its
genuine free-unit component. -/
theorem extension_forward (P : C) (N : Mod C A.X) :
    parameterExtension A P ((Mod.internalHomOfEqualizer A ((Mod.free A.X).obj P)).obj N).X N
        (MonoidalClosed.uncurry (forward A P N)) =
      MonoidalClosed.uncurry (Mod.internalHomι A ((Mod.free A.X).obj P) N) := by
  let F := (Mod.free A.X).obj P
  let H := (Mod.internalHomOfEqualizer A F).obj N
  let E := (ihom (A.X ⊗ P)).obj N.X
  let j : H.X ⟶ E := Mod.internalHomι A F N
  let g : (A.X ⊗ P) ⊗ H.X ⟶ N.X := MonoidalClosed.uncurry j
  let s : A.X ⊗ (A.X ⊗ P) ⟶ A.X ⊗ P := F.mod.smul
  have h := Mod.internalHom_condition A F N
  change j ≫ (MonoidalClosed.pre s).app N.X =
    j ≫ MonoidalClosed.curry
      ((α_ A.X (A.X ⊗ P) E).hom ≫ (A.X ◁ (ihom.ev (A.X ⊗ P)).app N.X) ≫
        N.mod.smul) at h
  have hu := congrArg MonoidalClosed.uncurry h
  rw [MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry] at hu
  change (s ▷ H.X) ≫ g =
    ((A.X ⊗ (A.X ⊗ P)) ◁ j) ≫ (α_ A.X (A.X ⊗ P) E).hom ≫
      (A.X ◁ (ihom.ev (A.X ⊗ P)).app N.X) ≫ N.mod.smul at hu
  rw [associator_naturality_right_assoc, ← whiskerLeft_comp_assoc,
    ← MonoidalClosed.uncurry_eq] at hu
  change (s ▷ H.X) ≫ g =
    (α_ A.X (A.X ⊗ P) H.X).hom ≫ (A.X ◁ g) ≫ N.mod.smul at hu
  have hq : MonoidalClosed.uncurry (forward A P N) = (generator A P ▷ H.X) ≫ g := by
    change MonoidalClosed.uncurry
      (j ≫ (MonoidalClosed.pre (generator A P)).app N.X) = _
    exact MonoidalClosed.uncurry_pre_app N.X j (generator A P)
  have hs : (A.X ◁ generator A P) ≫ s = 𝟙 (A.X ⊗ P) := generator_action A P
  change parameterExtension A P H.X N (MonoidalClosed.uncurry (forward A P N)) = g
  simp only [parameterExtension, hq, whiskerLeft_comp, Category.assoc]
  rw [
    ← associator_naturality_middle_assoc, ← hu,
    ← comp_whiskerRight_assoc, hs, id_whiskerRight, Category.id_comp]

/-- Full original free extension followed by original free-unit evaluation recovers the entire
coefficient internal Hom. -/
theorem inverse_forward (P : C) (N : Mod C A.X) :
    inverse A P N ≫ forward A P N = 𝟙 _ := by
  let H := (Mod.internalHomOfEqualizer A ((Mod.free A.X).obj P)).obj N
  let j : H.X ⟶ (ihom (A.X ⊗ P)).obj N.X :=
    Mod.internalHomι A ((Mod.free A.X).obj P) N
  have hj : inverse A P N ≫ j = MonoidalClosed.curry
      (parameterExtension A P ((ihom P).obj N.X) N ((ihom.ev P).app N.X)) :=
    inverse_ι A P N
  change inverse A P N ≫ (j ≫ (MonoidalClosed.pre (generator A P)).app N.X) = _
  rw [← Category.assoc, hj]
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_curry,
    parameterExtension_generator]
  exact (MonoidalClosed.uncurry_id_eq_ev P N.X).symm

/-- Original free-unit evaluation followed by full extension recovers the actual original module
internal-Hom equalizer. -/
theorem forward_inverse (P : C) (N : Mod C A.X) :
    forward A P N ≫ inverse A P N = 𝟙 _ := by
  let H := (Mod.internalHomOfEqualizer A ((Mod.free A.X).obj P)).obj N
  let j : H.X ⟶ (ihom (A.X ⊗ P)).obj N.X :=
    Mod.internalHomι A ((Mod.free A.X).obj P) N
  apply Fork.IsLimit.hom_ext (Mod.internalHomIsLimit A ((Mod.free A.X).obj P) N)
  change (forward A P N ≫ inverse A P N) ≫ j = (𝟙 H.X) ≫ j
  have hj : inverse A P N ≫ j = MonoidalClosed.curry
      (parameterExtension A P ((ihom P).obj N.X) N ((ihom.ev P).app N.X)) :=
    inverse_ι A P N
  rw [Category.assoc, hj, Category.id_comp]
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
  change ((A.X ⊗ P) ◁ forward A P N) ≫
      parameterExtension A P ((ihom P).obj N.X) N ((ihom.ev P).app N.X) =
    MonoidalClosed.uncurry j
  rw [parameterExtension_precompose, ← MonoidalClosed.uncurry_eq, extension_forward]
  rfl

/-- The actual free-source module internal Hom is isomorphic to the original coefficient internal
Hom through original unit evaluation and original equalizer extension. -/
def iso (P : C) (N : Mod C A.X) :
    ((Mod.internalHomOfEqualizer A ((Mod.free A.X).obj P)).obj N).X ≅ (ihom P).obj N.X where
  hom := forward A P N
  inv := inverse A P N
  hom_inv_id := forward_inverse A P N
  inv_hom_id := inverse_forward A P N

/-- Original free-unit evaluation retains the entire actual scalar action of the original module
internal Hom. -/
theorem forward_linear (P : C) (N : Mod C A.X) :
    ((Mod.internalHomOfEqualizer A ((Mod.free A.X).obj P)).obj N).mod.smul ≫ forward A P N =
      (A.X ◁ forward A P N) ≫ (Mod.internalHomAuxiliary A P N).mod.smul := by
  let F := (Mod.free A.X).obj P
  let H := (Mod.internalHomOfEqualizer A F).obj N
  let j : H.X ⟶ (ihom (A.X ⊗ P)).obj N.X := Mod.internalHomι A F N
  let p : (ihom (A.X ⊗ P)).obj N.X ⟶ (ihom P).obj N.X :=
    (MonoidalClosed.pre (generator A P)).app N.X
  have hj : H.mod.smul ≫ j = (A.X ◁ j) ≫ (Mod.internalHomAuxiliary A (A.X ⊗ P) N).mod.smul :=
    Mod.internalHomι_smul A F N
  have hp : (Mod.internalHomAuxiliary A (A.X ⊗ P) N).mod.smul ≫ p =
      (A.X ◁ p) ≫ (Mod.internalHomAuxiliary A P N).mod.smul :=
    Mod.internalHomAuxiliary_pre_linear A (A.X ⊗ P) P (generator A P) N
  change H.mod.smul ≫ (j ≫ p) =
    (A.X ◁ (j ≫ p)) ≫ (Mod.internalHomAuxiliary A P N).mod.smul
  rw [← Category.assoc, hj, Category.assoc, hp, whiskerLeft_comp, Category.assoc]

/-- Actual free-unit evaluation retains every original whole target-module morphism. -/
theorem forward_naturality (P : C) {N N' : Mod C A.X} (f : N ⟶ N') :
    ((Mod.internalHomOfEqualizer A ((Mod.free A.X).obj P)).map f).hom ≫ forward A P N' =
      forward A P N ≫ (ihom P).map f.hom := by
  let H := Mod.internalHomOfEqualizer A ((Mod.free A.X).obj P)
  let j : (H.obj N).X ⟶ (ihom (A.X ⊗ P)).obj N.X :=
    Mod.internalHomι A ((Mod.free A.X).obj P) N
  let j' : (H.obj N').X ⟶ (ihom (A.X ⊗ P)).obj N'.X :=
    Mod.internalHomι A ((Mod.free A.X).obj P) N'
  let g : (H.obj N).X ⟶ (H.obj N').X := (H.map f).hom
  have hg : g ≫ j' = j ≫ (ihom (A.X ⊗ P)).map f.hom :=
    Mod.internalHomMap A ((Mod.free A.X).obj P) f
  change g ≫ (j' ≫ (MonoidalClosed.pre (generator A P)).app N'.X) =
    (j ≫ (MonoidalClosed.pre (generator A P)).app N.X) ≫ (ihom P).map f.hom
  rw [← Category.assoc, hg, Category.assoc, Category.assoc]
  exact congrArg (fun h => j ≫ h)
    ((MonoidalClosed.pre (generator A P)).naturality f.hom)

/-- Full original equalizer extension retains the same entire target-module morphism family. -/
theorem inverse_naturality (P : C) {N N' : Mod C A.X} (f : N ⟶ N') :
    (ihom P).map f.hom ≫ inverse A P N' =
      inverse A P N ≫ ((Mod.internalHomOfEqualizer A ((Mod.free A.X).obj P)).map f).hom := by
  apply (cancel_mono (iso A P N').hom).1
  change ((ihom P).map f.hom ≫ inverse A P N') ≫ forward A P N' =
    (inverse A P N ≫ ((Mod.internalHomOfEqualizer A ((Mod.free A.X).obj P)).map f).hom) ≫
      forward A P N'
  rw [Category.assoc, inverse_forward, Category.comp_id, Category.assoc,
    forward_naturality, ← Category.assoc, inverse_forward, Category.id_comp]

/-- The original unit evaluation and complete equalizer extension assemble into a genuine full
target-natural comparison of actual free-source internal-Hom functors. -/
def comparison (P : C) :
    Mod.internalHomOfEqualizer A ((Mod.free A.X).obj P) ⋙ Mod.forget (D := C) A.X ≅
      Mod.forget (D := C) A.X ⋙ ihom P :=
  NatIso.ofComponents (iso A P) (by
    intro N N' f
    exact forward_naturality A P f)

/-- Both original comparison maps are inverse module morphisms into the actual
original auxiliary module. -/
def moduleIso (P : C) (N : Mod C A.X) :
    (Mod.internalHomOfEqualizer A ((Mod.free A.X).obj P)).obj N ≅
      Mod.internalHomAuxiliary A P N := by
  let H := (Mod.internalHomOfEqualizer A ((Mod.free A.X).obj P)).obj N
  let K := Mod.internalHomAuxiliary A P N
  letI : ModObj A.X H.X := H.mod
  letI : ModObj A.X K.X := K.mod
  let e : H.X ≅ K.X := iso A P N
  have h : H.mod.smul ≫ e.hom = (A.X ◁ e.hom) ≫ K.mod.smul := forward_linear A P N
  letI : IsModHom A.X e.hom := ⟨h⟩
  have hInv : K.mod.smul ≫ e.inv = (A.X ◁ e.inv) ≫ H.mod.smul :=
    IsModHom.smul_hom (A := A.X) (f := e.inv)
  exact
    { hom := Mod.Hom.mk' e.hom h
      inv := Mod.Hom.mk' e.inv hInv
      hom_inv_id := by
        apply Mod.hom_ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply Mod.hom_ext
        exact e.inv_hom_id }

section Source
variable [HasCoequalizers C]

/-- The selected module tensor is the original balanced relative tensor. -/
local instance originalModuleMonoidal : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
/-- The selected module closed structure is the original balanced adjunction. -/
local instance originalModuleClosed : MonoidalClosed (Mod C A.X) := Mod.instMonoidalClosed A

/-- The existing original balanced evaluation is exactly uncurrying its original internal-Hom
equalizer projection. This exposes the original evaluation characteristic used by its existing
adjunction proof. -/
theorem evaluation_projection (M N : Mod C A.X) :
    Mod.relativeTensorπ A M ((Mod.internalHomOfEqualizer A M).obj N) ≫
        ((Mod.evaluation A M).app N).hom =
      MonoidalClosed.uncurry (Mod.internalHomι A M N) := by
  dsimp only [Mod.evaluation]
  apply Mod.relativeTensorDesc_π

/-- Every entire original source-module arrow induces the actual base internal-Hom pre-map after
the original equalizer projection. -/
theorem precompose_projection {M M' : Mod C A.X} (f : M ⟶ M') (N : Mod C A.X) :
    ((MonoidalClosed.pre f).app N).hom ≫ Mod.internalHomι A M N =
      Mod.internalHomι A M' N ≫ (MonoidalClosed.pre f.hom).app N.X := by
  let HM := (Mod.internalHomOfEqualizer A M).obj N
  let HM' := (Mod.internalHomOfEqualizer A M').obj N
  let p : HM' ⟶ HM := (MonoidalClosed.pre f).app N
  let j : HM.X ⟶ (ihom M.X).obj N.X := Mod.internalHomι A M N
  let j' : HM'.X ⟶ (ihom M'.X).obj N.X := Mod.internalHomι A M' N
  have hclosed : (M ◁ p) ≫ (Mod.evaluation A M).app N =
      (f ▷ HM') ≫ (Mod.evaluation A M').app N :=
    MonoidalClosed.id_tensor_pre_app_comp_ev f N
  have hl : Mod.relativeTensorMap A (𝟙 M) p = M ◁ p := id_tensorHom M p
  have hr : Mod.relativeTensorMap A f (𝟙 HM') = f ▷ HM' := tensorHom_id f HM'
  have hπl := Mod.relativeTensorMap_π A (𝟙 M) p
  have hπr := Mod.relativeTensorMap_π A f (𝟙 HM')
  rw [hl] at hπl
  rw [hr] at hπr
  simp only [Mod.id_hom', id_tensorHom] at hπl
  simp only [Mod.id_hom', tensorHom_id] at hπr
  have h := congrArg
    (fun g : ((Mod.relativeTensor A).obj M).obj HM' ⟶ N =>
      Mod.relativeTensorπ A M HM' ≫ g.hom) hclosed
  simp only [Mod.comp_hom'] at h
  rw [reassoc_of% hπl, reassoc_of% hπr, evaluation_projection, evaluation_projection] at h
  change p.hom ≫ j = j' ≫ (MonoidalClosed.pre f.hom).app N.X
  apply MonoidalClosed.uncurry_injective (A := M.X)
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_pre_app]
  exact h

/-- Every entire original free-source module arrow acts by its actual original unit adjunct after
the complete module internal-Hom projection. -/
theorem forward_precompose {P P' : C}
    (f : (Mod.free A.X).obj P' ⟶ (Mod.free A.X).obj P) (N : Mod C A.X) :
    ((MonoidalClosed.pre f).app N).hom ≫ forward A P' N =
      Mod.internalHomι A ((Mod.free A.X).obj P) N ≫
        (MonoidalClosed.pre (generator A P' ≫ f.hom)).app N.X := by
  let F := (Mod.free A.X).obj P
  let F' := (Mod.free A.X).obj P'
  let H := (Mod.internalHomOfEqualizer A F).obj N
  let H' := (Mod.internalHomOfEqualizer A F').obj N
  let p : H ⟶ H' := (MonoidalClosed.pre f).app N
  let j : H.X ⟶ (ihom F.X).obj N.X := Mod.internalHomι A F N
  let j' : H'.X ⟶ (ihom F'.X).obj N.X := Mod.internalHomι A F' N
  let g : P' ⟶ F'.X := generator A P'
  have hp : p.hom ≫ j' = j ≫ (MonoidalClosed.pre f.hom).app N.X :=
    precompose_projection A f N
  have hpre : (MonoidalClosed.pre f.hom).app N.X ≫ (MonoidalClosed.pre g).app N.X =
      (MonoidalClosed.pre (g ≫ f.hom)).app N.X := by
    have h := congrArg (fun t : ihom F.X ⟶ ihom P' => t.app N.X)
      (MonoidalClosed.pre_map g f.hom)
    simpa only [NatTrans.comp_app] using h.symm
  change p.hom ≫ (j' ≫ (MonoidalClosed.pre g).app N.X) =
    j ≫ (MonoidalClosed.pre (g ≫ f.hom)).app N.X
  rw [← Category.assoc, hp, Category.assoc, hpre]

/-- Original free-source coefficient arrows retain their full contravariant internal-Hom maps
through original free-unit evaluation. -/
theorem forward_free_map {P P' : C} (f : P' ⟶ P) (N : Mod C A.X) :
    ((MonoidalClosed.pre ((Mod.free A.X).map f)).app N).hom ≫ forward A P' N =
      forward A P N ≫ (MonoidalClosed.pre f).app N.X := by
  have hg : generator A P' ≫ ((Mod.free A.X).map f).hom = f ≫ generator A P :=
    ((Mod.freeForgetAdjunction A.X).unit.naturality f).symm
  rw [forward_precompose, hg]
  have h := congrArg
    (fun t : ihom ((Mod.free A.X).obj P).X ⟶ ihom P' => t.app N.X)
    (MonoidalClosed.pre_map f (generator A P))
  change Mod.internalHomι A ((Mod.free A.X).obj P) N ≫
      (MonoidalClosed.pre (f ≫ generator A P)).app N.X =
    (Mod.internalHomι A ((Mod.free A.X).obj P) N ≫
      (MonoidalClosed.pre (generator A P)).app N.X) ≫ (MonoidalClosed.pre f).app N.X
  rw [h, NatTrans.comp_app]
  exact (Category.assoc _ _ _).symm

end Source

end CategoryTheory.Mod.FreeInternalHom
