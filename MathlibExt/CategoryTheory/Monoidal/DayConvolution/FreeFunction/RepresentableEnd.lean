/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Limits.Shapes.End
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# Internal Hom ends from free diagrams

Given the required copowers and end, the end of the internal-Hom diagram from the free
diagram at r with coefficient M into G is isomorphic to the internal Hom from M into G(r).
The forward map evaluates the identity-index coproduct summand, and the inverse extends a
coefficient map along every index morphism. Both maps are inverse and natural in G, with
explicit formulas on the end projections.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uI vI uV vV
open CategoryTheory MonoidalCategory Limits Opposite
open scoped MonoidalClosed

namespace NativeOmegaPreparation.OrdinaryFreeEnd
variable {I : Type uI} [Category.{vI} I]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  [MonoidalClosed V] [∀ a b : I, HasCoproductsOfShape (a ⟶ b) V]
  (r : I) (M : V) (G : I ⥤ V)

/-- The actual ordinary free-diagram internal-Hom bifunctor uses the original evaluation left
adjoint and every original target map. -/
def diagram : Iᵒᵖ ⥤ I ⥤ V :=
  Functor.whiskeringLeft₂ _ |>.obj ((evaluationLeftAdjoint V r).obj M).op |>.obj G |>.obj
    MonoidalClosed.internalHom

/-- A genuine entire target transformation acts through the original closed internal-Hom diagram. -/
def diagramMap {G' : I ⥤ V} (h : G ⟶ G') : diagram r M G ⟶ diagram r M G' :=
  Functor.whiskeringLeft₂ _ |>.obj ((evaluationLeftAdjoint V r).obj M).op |>.map h |>.app
    MonoidalClosed.internalHom

/-- The original parameterized free extension descends the actual tensor-preserved coproduct,
keeping each original index arrow. -/
def parameterExtension (T : V) (q : M ⊗ T ⟶ G.obj r) (b : I) :
    (∐ fun _ : r ⟶ b => M) ⊗ T ⟶ G.obj b :=
  (preservesColimitIso (tensorRight T)
      (Discrete.functor (fun _ : r ⟶ b => M))).hom ≫
    (Sigma.isoColimit
      ((Discrete.functor (fun _ : r ⟶ b => M)) ⋙ tensorRight T)).inv ≫
    Sigma.desc (fun f : r ⟶ b => q ≫ G.map f)

/-- Every entire original coproduct generator retains its actual target index action after
parameterized extension. -/
@[reassoc]
theorem parameterExtension_ι (T : V) (q : M ⊗ T ⟶ G.obj r) (b : I) (f : r ⟶ b) :
    (Sigma.ι (fun _ : r ⟶ b => M) f ▷ T) ≫ parameterExtension r M G T q b =
      q ≫ G.map f := by
  change (tensorRight T).map (Sigma.ι (fun _ : r ⟶ b => M) f) ≫ _ = _
  simp only [parameterExtension]
  rw [ι_preservesColimitIso_hom_assoc,
    Sigma.ι_isoColimit_inv_assoc, Sigma.ι_comp_desc]

private theorem tensor_hom_ext (T : V) (b : I) {Z : V}
    {f g : (∐ fun _ : r ⟶ b => M) ⊗ T ⟶ Z}
    (h : ∀ a : r ⟶ b,
      (Sigma.ι (fun _ : r ⟶ b => M) a ▷ T) ≫ f =
        (Sigma.ι (fun _ : r ⟶ b => M) a ▷ T) ≫ g) : f = g := by
  apply (cancel_epi (preservesColimitIso (tensorRight T)
    (Discrete.functor (fun _ : r ⟶ b => M))).inv).mp
  apply colimit.hom_ext
  rintro ⟨a⟩
  simp only [ι_preservesColimitIso_inv_assoc]
  change (Sigma.ι (fun _ : r ⟶ b => M) a ▷ T) ≫ f =
    (Sigma.ι (fun _ : r ⟶ b => M) a ▷ T) ≫ g
  exact h a

omit [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V] in
/-- The original free diagram carries every complete injection by actual postcomposition of index
arrows. -/
@[reassoc]
theorem free_ι_map {b c : I} (g : b ⟶ c) (f : r ⟶ b) :
    Sigma.ι (fun _ : r ⟶ b => M) f ≫
        ((evaluationLeftAdjoint V r).obj M).map g =
      Sigma.ι (fun _ : r ⟶ c => M) (f ≫ g) := by
  change Sigma.ι (fun _ : r ⟶ b => M) f ≫
    Sigma.desc (fun h => Sigma.ι (fun _ : r ⟶ c => M) (h ≫ g)) = _
  rw [Sigma.ι_comp_desc]

/-- The entire original parameterized extension is natural on every actual target index arrow. -/
theorem parameterExtension_naturality (T : V) (q : M ⊗ T ⟶ G.obj r)
    {b c : I} (g : b ⟶ c) :
    (((evaluationLeftAdjoint V r).obj M).map g ▷ T) ≫
        parameterExtension r M G T q c =
      parameterExtension r M G T q b ≫ G.map g := by
  change (Sigma.desc (fun f : r ⟶ b =>
    Sigma.ι (fun _ : r ⟶ c => M) (f ≫ g)) ▷ T) ≫
      parameterExtension r M G T q c = parameterExtension r M G T q b ≫ G.map g
  apply tensor_hom_ext r M T b
  intro f
  rw [← Category.assoc, ← comp_whiskerRight, Sigma.ι_comp_desc,
    parameterExtension_ι, parameterExtension_ι_assoc]
  rw [G.map_comp]

/-- Original parameterized free extension assembles into a genuine wedge on the unchanged
internal-Hom diagram. -/
theorem parameterExtension_condition (T : V) (q : M ⊗ T ⟶ G.obj r)
    {b c : I} (g : b ⟶ c) :
    MonoidalClosed.curry (parameterExtension r M G T q b) ≫
        ((diagram r M G).obj (.op b)).map g =
      MonoidalClosed.curry (parameterExtension r M G T q c) ≫
        ((diagram r M G).map g.op).app c := by
  change MonoidalClosed.curry (parameterExtension r M G T q b) ≫
      (ihom (∐ fun _ : r ⟶ b => M)).map (G.map g) =
    MonoidalClosed.curry (parameterExtension r M G T q c) ≫
      (MonoidalClosed.pre (Sigma.desc (fun f : r ⟶ b =>
        Sigma.ι (fun _ : r ⟶ c => M) (f ≫ g)))).app (G.obj c)
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_right, MonoidalClosed.uncurry_pre_app,
    MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry]
  exact (parameterExtension_naturality r M G T q g).symm

/-- Parameterized extension retains every whole parameter map before its original coefficient
evaluation. -/
theorem parameterExtension_precompose {T T' : V} (f : T' ⟶ T)
    (q : M ⊗ T ⟶ G.obj r) (b : I) :
    ((∐ fun _ : r ⟶ b => M) ◁ f) ≫ parameterExtension r M G T q b =
      parameterExtension r M G T' ((M ◁ f) ≫ q) b := by
  apply tensor_hom_ext r M T' b
  intro g
  rw [← whisker_exchange_assoc, parameterExtension_ι, parameterExtension_ι]
  rw [Category.assoc]

variable [HasEnd (diagram r M G)]

/-- Original free-diagram end evaluation uses the literal identity-index coproduct insertion. -/
def forward : end_ (diagram r M G) ⟶ (ihom M).obj (G.obj r) :=
  end_.π (diagram r M G) r ≫
    (MonoidalClosed.pre (Sigma.ι (fun _ : r ⟶ r => M) (𝟙 r))).app (G.obj r)

/-- The inverse comparison is the genuine end lift of every original free-diagram extension. -/
def inverse : (ihom M).obj (G.obj r) ⟶ end_ (diagram r M G) :=
  end_.lift (fun b => MonoidalClosed.curry
    (parameterExtension r M G ((ihom M).obj (G.obj r)) ((ihom.ev M).app (G.obj r)) b))
    (fun _ _ g => parameterExtension_condition r M G _ _ g)

/-- Every inverse end projection is the actual coproduct extension of the original coefficient
evaluation. -/
@[reassoc]
theorem inverse_π (b : I) :
    inverse r M G ≫ end_.π (diagram r M G) b =
      MonoidalClosed.curry
        (parameterExtension r M G ((ihom M).obj (G.obj r)) ((ihom.ev M).app (G.obj r)) b) :=
  end_.lift_π _ _ b

/-- Every original free-end projection is reconstructed from free evaluation and the full family of
index-arrow generators. -/
theorem extension_forward (b : I) :
    parameterExtension r M G (end_ (diagram r M G))
        (MonoidalClosed.uncurry (forward r M G)) b =
      MonoidalClosed.uncurry (end_.π (diagram r M G) b) := by
  let E := end_ (diagram r M G)
  let p (a : I) : E ⟶ (ihom (∐ fun _ : r ⟶ a => M)).obj (G.obj a) :=
    end_.π (diagram r M G) a
  have hq : MonoidalClosed.uncurry (forward r M G) =
      (Sigma.ι (fun _ : r ⟶ r => M) (𝟙 r) ▷ E) ≫ MonoidalClosed.uncurry (p r) := by
    change MonoidalClosed.uncurry
      (p r ≫ (MonoidalClosed.pre (Sigma.ι (fun _ : r ⟶ r => M) (𝟙 r))).app
        (G.obj r)) = _
    exact MonoidalClosed.uncurry_pre_app _ _ _
  apply tensor_hom_ext r M E b
  intro f
  have h := end_.condition (diagram r M G) f
  change p r ≫ (ihom (∐ fun _ : r ⟶ r => M)).map (G.map f) =
    p b ≫ (MonoidalClosed.pre (Sigma.desc (fun g : r ⟶ r =>
      Sigma.ι (fun _ : r ⟶ b => M) (g ≫ f)))).app (G.obj b) at h
  have hu := congrArg MonoidalClosed.uncurry h
  rw [MonoidalClosed.uncurry_natural_right, MonoidalClosed.uncurry_pre_app] at hu
  change (Sigma.ι (fun _ : r ⟶ b => M) f ▷ E) ≫
      parameterExtension r M G E (MonoidalClosed.uncurry (forward r M G)) b =
    (Sigma.ι (fun _ : r ⟶ b => M) f ▷ E) ≫ MonoidalClosed.uncurry (p b)
  rw [parameterExtension_ι, hq, Category.assoc, hu,
    ← Category.assoc, ← comp_whiskerRight, Sigma.ι_comp_desc, Category.id_comp]

/-- Extension followed by the original identity-index evaluation recovers the entire coefficient
internal Hom. -/
theorem inverse_forward : inverse r M G ≫ forward r M G = 𝟙 _ := by
  let p : end_ (diagram r M G) ⟶
      (ihom (∐ fun _ : r ⟶ r => M)).obj (G.obj r) := end_.π (diagram r M G) r
  change inverse r M G ≫
    (p ≫ (MonoidalClosed.pre (Sigma.ι (fun _ : r ⟶ r => M) (𝟙 r))).app (G.obj r)) = _
  have hp : inverse r M G ≫ p = MonoidalClosed.curry
      (parameterExtension r M G ((ihom M).obj (G.obj r)) ((ihom.ev M).app (G.obj r)) r) :=
    inverse_π r M G r
  rw [← Category.assoc, hp]
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_curry,
    parameterExtension_ι, G.map_id, Category.comp_id]
  exact (MonoidalClosed.uncurry_id_eq_ev M (G.obj r)).symm

/-- Original evaluation followed by extension recovers every complete end projection and therefore
the actual end object. -/
theorem forward_inverse : forward r M G ≫ inverse r M G = 𝟙 _ := by
  apply end_.hom_ext
  intro b
  let p : end_ (diagram r M G) ⟶
      (ihom (∐ fun _ : r ⟶ b => M)).obj (G.obj b) := end_.π (diagram r M G) b
  change (forward r M G ≫ inverse r M G) ≫ p = (𝟙 (end_ (diagram r M G))) ≫ p
  have hp : inverse r M G ≫ p = MonoidalClosed.curry
      (parameterExtension r M G ((ihom M).obj (G.obj r)) ((ihom.ev M).app (G.obj r)) b) :=
    inverse_π r M G b
  rw [Category.assoc, hp, Category.id_comp]
  rw [← MonoidalClosed.curry_natural_left]
  rw [parameterExtension_precompose]
  rw [← MonoidalClosed.uncurry_eq, extension_forward]
  change MonoidalClosed.curry (MonoidalClosed.uncurry p) = p
  exact MonoidalClosed.curry_uncurry p

/-- The original free-diagram end and coefficient internal Hom are isomorphic through the actual
evaluation and full generator extension maps. -/
def iso : end_ (diagram r M G) ≅ (ihom M).obj (G.obj r) where
  hom := forward r M G
  inv := inverse r M G
  hom_inv_id := forward_inverse r M G
  inv_hom_id := inverse_forward r M G

omit [BraidedCategory V] in
/-- Original free-end evaluation is natural under every complete target transformation. -/
theorem forward_naturality {G' : I ⥤ V} [HasEnd (diagram r M G')]
    (h : G ⟶ G') :
    end_.map (diagramMap r M G h) ≫ forward r M G' =
      forward r M G ≫ (ihom M).map (h.app r) := by
  let p : end_ (diagram r M G) ⟶
      (ihom (∐ fun _ : r ⟶ r => M)).obj (G.obj r) := end_.π (diagram r M G) r
  let p' : end_ (diagram r M G') ⟶
      (ihom (∐ fun _ : r ⟶ r => M)).obj (G'.obj r) := end_.π (diagram r M G') r
  have hp : end_.map (diagramMap r M G h) ≫ p' =
      p ≫ (ihom (∐ fun _ : r ⟶ r => M)).map (h.app r) :=
    end_.map_π (diagramMap r M G h) r
  change end_.map (diagramMap r M G h) ≫
      (p' ≫ (MonoidalClosed.pre (Sigma.ι (fun _ : r ⟶ r => M) (𝟙 r))).app (G'.obj r)) =
    (p ≫ (MonoidalClosed.pre (Sigma.ι (fun _ : r ⟶ r => M) (𝟙 r))).app (G.obj r)) ≫
      (ihom M).map (h.app r)
  rw [← Category.assoc, hp, Category.assoc, Category.assoc]
  exact congrArg (fun f => p ≫ f)
    ((MonoidalClosed.pre (Sigma.ι (fun _ : r ⟶ r => M) (𝟙 r))).naturality (h.app r))

/-- Original full generator extension is natural under the same complete target transformation. -/
theorem inverse_naturality {G' : I ⥤ V} [HasEnd (diagram r M G')]
    (h : G ⟶ G') :
    (ihom M).map (h.app r) ≫ inverse r M G' =
      inverse r M G ≫ end_.map (diagramMap r M G h) := by
  apply (cancel_mono (iso r M G').hom).1
  change ((ihom M).map (h.app r) ≫ inverse r M G') ≫ forward r M G' =
    (inverse r M G ≫ end_.map (diagramMap r M G h)) ≫ forward r M G'
  rw [Category.assoc, inverse_forward, Category.comp_id, Category.assoc,
    forward_naturality, ← Category.assoc, inverse_forward, Category.id_comp]

end NativeOmegaPreparation.OrdinaryFreeEnd
