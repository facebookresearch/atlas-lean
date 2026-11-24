/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoend

/-!
# Original coend maps along an enriched index functor

Both complete enriched relation faces are retained when the actual index,
weight and coefficient maps descend to the selected coends.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uV vV uA uB
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.weightedCoend.Transport

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]
  (T : EnrichedFunctor V A B)
  (W : EnrichedFunctor V Aᵒᵖ V) (W' : EnrichedFunctor V Bᵒᵖ V)
  (Q : EnrichedFunctor V A V) (Q' : EnrichedFunctor V B V)
  (w : ∀ a, W.obj (op a) ⟶ W'.obj (op (T.obj a)))
  (q : ∀ a, Q.obj a ⟶ Q'.obj (T.obj a))

/-- The original weight and coefficient maps on every object summand. -/
abbrev objectMap (a : A) : Enriched.weightedCoend.objects W Q a ⟶
    Enriched.weightedCoend.objects W' Q' (T.obj a) := w a ⊗ₘ q a

/-- The index map acts on the whole Hom factor in every original relation summand. -/
abbrev relationMap (a b : A) : Enriched.weightedCoend.relations W Q (a, b) ⟶
    Enriched.weightedCoend.relations W' Q' (T.obj a, T.obj b) :=
  w b ⊗ₘ (T.map a b ⊗ₘ q a)

variable
  (hW : ∀ a b,
    MonoidalClosed.uncurry (W.map (op b) (op a)) ≫ w a =
      (w b ⊗ₘ T.map a b) ≫ MonoidalClosed.uncurry (W'.map (op (T.obj b)) (op (T.obj a))))
  (hQ : ∀ a b,
    MonoidalClosed.uncurry (Q.map a b) ≫ q b =
      (q a ⊗ₘ T.map a b) ≫ MonoidalClosed.uncurry (Q'.map (T.obj a) (T.obj b)))

include hW hQ

omit hQ in
/-- The complete weight face commutes with the actual enriched index map. -/
@[reassoc]
theorem face0 (a b : A) :
    Enriched.weightedCoend.face0 W Q a b ≫ objectMap T W W' Q Q' w q a =
      relationMap T W W' Q Q' w q a b ≫ Enriched.weightedCoend.face0 W' Q' (T.obj a) (T.obj b) := by
  simp only [Enriched.weightedCoend.face0, objectMap, relationMap, Category.assoc]
  rw [associator_inv_naturality_assoc]
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  simp only [Category.id_comp, Category.comp_id]
  rw [hW a b]

omit hW in
/-- The complete coefficient-action face commutes on the full original Hom object. -/
@[reassoc]
theorem face1 (a b : A) :
    Enriched.weightedCoend.face1 W Q a b ≫ objectMap T W W' Q Q' w q b =
      relationMap T W W' Q Q' w q a b ≫ Enriched.weightedCoend.face1 W' Q' (T.obj a) (T.obj b) := by
  have ha : (β_ (a ⟶[V] b) (Q.obj a)).hom ≫
      MonoidalClosed.uncurry (Q.map a b) ≫ q b =
      (T.map a b ⊗ₘ q a) ≫ (β_ (T.obj a ⟶[V] T.obj b) (Q'.obj (T.obj a))).hom ≫
        MonoidalClosed.uncurry (Q'.map (T.obj a) (T.obj b)) := by
    rw [hQ a b]
    exact (BraidedCategory.braiding_naturality_assoc (T.map a b) (q a)
      (MonoidalClosed.uncurry (Q'.map (T.obj a) (T.obj b)))).symm
  simp only [Enriched.weightedCoend.face1, objectMap, relationMap, ← id_tensorHom,
    tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  simpa only [Category.assoc] using congrArg (fun f => w b ⊗ₘ f) ha

variable [HasCoproduct (Enriched.weightedCoend.objects W Q)]
  [HasCoproduct (Enriched.weightedCoend.relations W Q)]
  [HasCoequalizer (Enriched.weightedCoend.leftMap W Q) (Enriched.weightedCoend.rightMap W Q)]
  [HasCoproduct (Enriched.weightedCoend.objects W' Q')]
  [HasCoproduct (Enriched.weightedCoend.relations W' Q')]
  [HasCoequalizer (Enriched.weightedCoend.leftMap W' Q') (Enriched.weightedCoend.rightMap W' Q')]

omit [HasCoproduct (Enriched.weightedCoend.objects W Q)]
  [HasCoproduct (Enriched.weightedCoend.relations W Q)]
  [HasCoequalizer (Enriched.weightedCoend.leftMap W Q)
    (Enriched.weightedCoend.rightMap W Q)] in
private theorem condition (a b : A) :
    Enriched.weightedCoend.face0 W Q a b ≫ objectMap T W W' Q Q' w q a ≫
        Enriched.weightedCoend.ι W' Q' (T.obj a) =
      Enriched.weightedCoend.face1 W Q a b ≫ objectMap T W W' Q Q' w q b ≫
        Enriched.weightedCoend.ι W' Q' (T.obj b) := by
  have h0 := face0_assoc T W W' Q Q' w q hW a b (Enriched.weightedCoend.ι W' Q' (T.obj a))
  have h1 := face1_assoc T W W' Q Q' w q hQ a b (Enriched.weightedCoend.ι W' Q' (T.obj b))
  have hc := congrArg (fun f => relationMap T W W' Q Q' w q a b ≫ f)
    (Enriched.weightedCoend.condition W' Q' (T.obj a) (T.obj b))
  simp only [Enriched.weightedCoend.face0, Enriched.weightedCoend.face1, Category.assoc]
    at h0 h1 hc ⊢
  exact h0.trans (hc.trans h1.symm)

/-- Descend the actual weight, coefficient and full index maps through the original coends. -/
@[no_expose]
def map : Enriched.weightedCoend W Q ⟶ Enriched.weightedCoend W' Q' :=
  Enriched.weightedCoend.desc W Q
    (fun a => objectMap T W W' Q Q' w q a ≫ Enriched.weightedCoend.ι W' Q' (T.obj a))
    (condition T W W' Q Q' w q hW hQ)

/-- The descended map retains every original generator with its original two factors. -/
@[reassoc]
theorem ι_map (a : A) :
    Enriched.weightedCoend.ι W Q a ≫ map T W W' Q Q' w q hW hQ =
      (w a ⊗ₘ q a) ≫ Enriched.weightedCoend.ι W' Q' (T.obj a) :=
  Enriched.weightedCoend.ι_desc W Q _ _ a

end CategoryTheory.Enriched.weightedCoend.Transport
