/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreePathNerveGeneratorCoordinates
import MathlibExt.Combinatorics.Quiver.PathPositionEndpoints

/-!
# Every full native original graph word is constant or an original generator restriction

The original full length-zero/one native path retains its individual
endpoints and whole generator. Complete original word recovery gives
the actual constant word or the SAME full native generator-cell
coefficient, at every original arity and ordinal operator.
-/

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial
namespace CategoryTheory.FreePathNerveCoordinates
variable (V : Type u) [Quiver.{v} V]

/-- The original one-generator cell is the SAME native full singleton path-word cell. -/
lemma generatorCell_eq_wordCell {x y : V} (f : x ⟶ y) :
    generatorCell V f = wordCell V f.toPath := by
  exact congrArg SSet.yonedaEquiv.symm (Quiver.Path.positionWord_toPath (V := V) f).symm

private lemma path_length_zero_heq {x y : V} (p : @Quiver.Path V inferInstance x y) (hp : p.length = 0) :
    HEq p (@Quiver.Path.nil V inferInstance x) := by
  cases p with
  | nil => rfl
  | cons p f => simp only [Quiver.Path.length_cons] at hp; omega

private lemma path_length_zero_const (n : ℕ) (w : (nerve (Paths V)) _⦋n⦌)
    (hw : (totalPath V n w).length = 0) :
    w = (Functor.const (Fin (n + 1))).obj (w.obj 0) := by
  change Fin (n + 1) ⥤ Paths V at w
  have hvertex : ∀ i : Fin (n + 1), w.obj i = w.obj 0 := by
    intro i
    have hp : (w.map (homOfLE (Fin.zero_le i))).length = 0 := by
      have hle := wordMap_length_le V n w (homOfLE (Fin.zero_le i))
      omega
    exact (@Quiver.Path.eq_of_length_zero V inferInstance _ _ (w.map (homOfLE (Fin.zero_le i))) hp).symm
  refine Functor.hext hvertex ?_
  intro i j f
  have hp : (w.map f).length = 0 := by
    have hle := wordMap_length_le V n w f
    omega
  have hm : HEq (w.map f) (𝟙 (w.obj i)) := by
    exact path_length_zero_heq V (w.map f) hp
  have hh : HEq (𝟙 (w.obj i)) (𝟙 (w.obj 0)) :=
    (eqToHom_heq_id_dom (C := Paths V) (w.obj i) (w.obj 0) (hvertex i)).symm.trans
      (eqToHom_heq_id_cod (C := Paths V) (w.obj i) (w.obj 0) (hvertex i))
  exact hm.trans hh

/-- Every full original graph word of total length zero is its SAME original constant vertex word. -/
theorem original_graph_word_constant (n : ℕ) (w : (nerve (Paths V)) _⦋n⦌)
    (hw : (totalPath V n w).length = 0) :
    w = (Functor.const (Fin (n + 1))).obj (w.obj 0) :=
  path_length_zero_const V n w hw

/-- A full original path of length one is its SAME actual original singleton generator. -/
lemma path_length_one_generator {x y : V} (p : @Quiver.Path V inferInstance x y) (hp : p.length = 1) :
    ∃ f : x ⟶ y, p = f.toPath := by
  cases p with
  | nil => cases hp
  | cons p f =>
    have hzero : p.length = 0 := by simpa only [Quiver.Path.length_cons] using Nat.succ.inj hp
    have hxy := Quiver.Path.eq_of_length_zero p hzero
    cases hxy
    have he := Quiver.Path.eq_nil_of_length_zero p hzero
    subst p
    exact ⟨f, rfl⟩

/-- Normalize only the ordinal codomain length of a SAME original singleton path. -/
private def singletonCuts {n : ℕ} {x y : V} (p : @Quiver.Path V inferInstance x y) (hp : p.length = 1)
    (cuts : Fin (n + 1) →o Fin (p.length + 1)) : Fin (n + 1) →o Fin 2 where
  toFun i := ⟨(cuts i).val, by have h := (cuts i).isLt; omega⟩
  monotone' := cuts.monotone

private lemma singletonCuts_restriction {n : ℕ} {x y : V}
    (p : @Quiver.Path V inferInstance x y) (f : x ⟶ y) (hp : p = f.toPath)
    (cuts : Fin (n + 1) →o Fin (p.length + 1)) :
    cuts.toFunctor ⋙ Quiver.Path.positionWord (V := V) p =
      (singletonCuts V p (congrArg Quiver.Path.length hp) cuts).toFunctor ⋙
        Quiver.Path.positionWord (V := V) f.toPath := by
  subst p
  rfl

/-- Every full original length-one word lies in its SAME original generator cell, retaining its actual coefficient. -/
theorem original_graph_word_generator (n : ℕ) (w : (nerve (Paths V)) _⦋n⦌)
    (hw : (totalPath V n w).length = 1) :
    ∃ f : @Quiver.Hom V inferInstance (w.obj 0) (w.obj (Fin.last n)),
      ∃ c : (Δ[1] : SSet.{max u v}) _⦋n⦌, (generatorCell V f).app (op ⦋n⦌) c = w := by
  change Fin (n + 1) ⥤ Paths V at w
  obtain ⟨f, hf⟩ := path_length_one_generator V (totalPath V n w) hw
  let c : (Δ[1] : SSet.{max u v}) _⦋n⦌ :=
    SSet.stdSimplex.objMk (singletonCuts V (totalPath V n w) hw (cutOrdinal V n w))
  refine ⟨f, c, ?_⟩
  have he : (generatorCell V f).app (op ⦋n⦌) c = (wordCell V f.toPath).app (op ⦋n⦌) c :=
    congrArg (fun F => F.app (op ⦋n⦌) c) (generatorCell_eq_wordCell V f)
  have hr := original_word_restriction V n w
  have hs := singletonCuts_restriction V (totalPath V n w) f hf (cutOrdinal V n w)
  have hc : (wordCell V f.toPath).app (op ⦋n⦌) c =
      (cutOrdinal V n w).toFunctor ⋙ Quiver.Path.positionWord (V := V) (totalPath V n w) := hs.symm
  exact he.trans (hc.trans hr.symm)

end CategoryTheory.FreePathNerveCoordinates
