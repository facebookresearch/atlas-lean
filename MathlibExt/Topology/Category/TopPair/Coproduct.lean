/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.CoproductEmbeddings
public import Mathlib.Topology.Category.TopPair

/-!
# Coproducts of topological pairs

Constructs coproducts of indexed families of topological pairs from the
coproducts of their ambient spaces and subspaces. Gives the component
inclusions and proves the resulting cofan is a colimit.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace TopPair

variable {ι : Type v} (P : ι → TopPair.{max v u})

/-- Explicit coproduct of a family of topological pairs. The ambient and subspace parts
are the TopCat coproducts of the respective parts, and the map is `Sigma.map` of the
pair maps. The embedding proof uses `TopCat.isEmbedding_sigmaMap`. -/
noncomputable def sigma : TopPair.{max v u} :=
  TopPair.of (Limits.Sigma.map (fun i => (P i).map))
    (TopCat.isEmbedding_sigmaMap (fun i => (P i).map) (fun i => (P i).isEmbedding_map))

/-- The canonical inclusion of a component pair into the explicit coproduct `sigma`. -/
noncomputable def sigmaι (i : ι) : P i ⟶ sigma P :=
  TopPair.ofHom (Limits.Sigma.ι (fun j => (P j).fst) i)
    (Limits.Sigma.ι (fun j => (P j).snd) i)
    (Limits.Sigma.ι_map (fun j => (P j).map) i)

@[simp]
theorem sigma_map : (sigma P).map = Limits.Sigma.map (fun i => (P i).map) :=
  rfl

@[simp]
theorem sigmaι_fst (i : ι) : Hom.fst (sigmaι P i) = Limits.Sigma.ι (fun j => (P j).fst) i :=
  rfl

@[simp]
theorem sigmaι_snd (i : ι) : Hom.snd (sigmaι P i) = Limits.Sigma.ι (fun j => (P j).snd) i :=
  rfl

/-- The cofan formed by the explicit coproduct `sigma` and its legs `sigmaι`. -/
noncomputable def sigmaCofan : Cofan P :=
  Cofan.mk (sigma P) (sigmaι P)

/-- The explicit cofan `sigmaCofan` is colimiting. -/
noncomputable def sigmaCofanIsColimit : IsColimit (sigmaCofan P) :=
  Cofan.IsColimit.mk (sigmaCofan P)
    (fun t =>
      let f := Limits.Sigma.desc (fun i => Hom.fst (t.inj i))
      let s := Limits.Sigma.desc (fun i => Hom.snd (t.inj i))
      have hw : s ≫ t.pt.map = (sigma P).map ≫ f := by
        apply Limits.Sigma.hom_ext
        intro i
        have h1 : Limits.Sigma.ι (fun j => (P j).snd) i ≫ s =
            Hom.snd (t.inj i) := Limits.Sigma.ι_comp_desc _ i
        have h2 : Limits.Sigma.ι (fun j => (P j).fst) i ≫ f =
            Hom.fst (t.inj i) := Limits.Sigma.ι_comp_desc _ i
        have hm : Limits.Sigma.ι (fun j => (P j).snd) i ≫
            Limits.Sigma.map (fun j => (P j).map) =
            (P i).map ≫ Limits.Sigma.ι (fun j => (P j).fst) i :=
          Limits.Sigma.ι_map _ i
        calc
          Limits.Sigma.ι (fun j => (P j).snd) i ≫ (s ≫ t.pt.map) =
              (Limits.Sigma.ι (fun j => (P j).snd) i ≫ s) ≫ t.pt.map := by
            rw [Category.assoc]
          _ = Hom.snd (t.inj i) ≫ t.pt.map := by rw [h1]
          _ = (P i).map ≫ Hom.fst (t.inj i) := (t.inj i).hom.w
          _ = (P i).map ≫ (Limits.Sigma.ι (fun j => (P j).fst) i ≫ f) := by rw [← h2]
          _ = ((P i).map ≫ Limits.Sigma.ι (fun j => (P j).fst) i) ≫ f := by
            rw [← Category.assoc]
          _ = (Limits.Sigma.ι (fun j => (P j).snd) i ≫
              Limits.Sigma.map (fun j => (P j).map)) ≫ f := by rw [← hm]
          _ = Limits.Sigma.ι (fun j => (P j).snd) i ≫
              (Limits.Sigma.map (fun j => (P j).map) ≫ f) := by rw [Category.assoc]
          _ = Limits.Sigma.ι (fun j => (P j).snd) i ≫ ((sigma P).map ≫ f) := rfl
      TopPair.ofHom f s hw)
    (fun t i => by
      simp only [sigmaCofan, cofan_mk_inj]
      apply MorphismProperty.Arrow.Hom.ext
      · exact Limits.Sigma.ι_comp_desc (fun j => Hom.snd (t.inj j)) i
      · exact Limits.Sigma.ι_comp_desc (fun j => Hom.fst (t.inj j)) i)
    (fun t m hm => by
      apply MorphismProperty.Arrow.Hom.ext
      · apply Limits.Sigma.hom_ext
        intro i
        have hmS := congrArg Hom.snd (hm i)
        have hiS : Hom.snd ((sigmaCofan P).inj i) =
            Limits.Sigma.ι (fun j => (P j).snd) i := by rfl
        have h1 : Limits.Sigma.ι (fun j => (P j).snd) i ≫ Hom.snd m =
            Hom.snd ((sigmaCofan P).inj i) ≫ Hom.snd m :=
          congrArg (· ≫ Hom.snd m) hiS.symm
        have h3 : Hom.snd ((sigmaCofan P).inj i ≫ m) = Hom.snd (t.inj i) := hmS
        have h4 : Hom.snd (t.inj i) =
            Limits.Sigma.ι (fun j => (P j).snd) i ≫
              Limits.Sigma.desc (fun j => Hom.snd (t.inj j)) :=
          (Limits.Sigma.ι_comp_desc (fun j => Hom.snd (t.inj j)) i).symm
        calc
          Limits.Sigma.ι (fun j => (P j).snd) i ≫ Hom.snd m = _ := h1
          _ = Hom.snd ((sigmaCofan P).inj i ≫ m) := rfl
          _ = _ := h3
          _ = _ := h4
      · apply Limits.Sigma.hom_ext
        intro i
        have hmF := congrArg Hom.fst (hm i)
        have hiF : Hom.fst ((sigmaCofan P).inj i) =
            Limits.Sigma.ι (fun j => (P j).fst) i := by rfl
        calc
          Limits.Sigma.ι (fun j => (P j).fst) i ≫ Hom.fst m =
              Hom.fst ((sigmaCofan P).inj i) ≫ Hom.fst m :=
            congrArg (· ≫ Hom.fst m) hiF.symm
          _ = Hom.fst ((sigmaCofan P).inj i ≫ m) := rfl
          _ = Hom.fst (t.inj i) := hmF
          _ = Limits.Sigma.ι (fun j => (P j).fst) i ≫
              Limits.Sigma.desc (fun j => Hom.fst (t.inj j)) :=
            (Limits.Sigma.ι_comp_desc (fun j => Hom.fst (t.inj j)) i).symm)

end TopPair
