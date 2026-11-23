/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Category.TopCat.Limits.Products

/-!
# Coproducts of topological embeddings

A coproduct of morphisms in `TopCat` whose underlying maps are embeddings
induces an embedding on the categorical coproduct map.
-/

@[expose] public section

open CategoryTheory Limits Topology

universe v u

namespace TopCat

variable {ι : Type v} {F G : ι → TopCat.{max v u}} (φ : ∀ i, F i ⟶ G i)

/-- An arbitrary coproduct of TopCat morphisms whose underlying functions are embeddings
induces an embedding on `Limits.Sigma.map`. Proved by conjugating the standard
`Topology.isEmbedding_sigmaMap` with the canonical `TopCat.sigmaIsoSigma` homeomorphisms. -/
theorem isEmbedding_sigmaMap (h : ∀ i, IsEmbedding (φ i)) :
    IsEmbedding (Limits.Sigma.map φ) := by
  let eF : (∐ F) ≅ TopCat.of (Σ i, F i) := TopCat.sigmaIsoSigma F
  let eG : (∐ G) ≅ TopCat.of (Σ i, G i) := TopCat.sigmaIsoSigma G
  have hcont : Continuous (Sigma.map (fun i : ι => i) (fun i => (φ i : F i → G i))) :=
    Continuous.sigma_map (fun i => (φ i).hom.continuous_toFun)
  let m : TopCat.of (Σ i, F i) ⟶ TopCat.of (Σ i, G i) :=
    TopCat.ofHom ⟨Sigma.map (fun i : ι => i) (fun i => (φ i : F i → G i)), hcont⟩
  have h_emb_sigma : IsEmbedding (Sigma.map (fun i : ι => i) (fun i => (φ i : F i → G i))) :=
    (Topology.isEmbedding_sigmaMap (Function.injective_id (α := ι))).mpr h
  have h_emb_m : IsEmbedding m := h_emb_sigma
  have h_emb_eF : IsEmbedding eF.hom :=
    (TopCat.homeoOfIso eF).isEmbedding
  have h_emb_eG_inv : IsEmbedding eG.inv :=
    (TopCat.homeoOfIso eG.symm).isEmbedding
  have h_m_apply : ∀ (i : ι) (x : F i), m ⟨i, x⟩ = ⟨i, (φ i) x⟩ := fun _ _ => rfl
  have h_sigmaι_apply : ∀ (i : ι) (x : F i), (TopCat.sigmaι F i) x = ⟨i, x⟩ := fun _ _ => rfl
  have h_eq : Limits.Sigma.map φ = eF.hom ≫ m ≫ eG.inv := by
    apply Sigma.hom_ext
    intro i
    calc
      Sigma.ι F i ≫ Limits.Sigma.map φ = φ i ≫ Sigma.ι G i :=
        Sigma.ι_map φ i
      _ = Sigma.ι F i ≫ (eF.hom ≫ m ≫ eG.inv) := by
        have hι : Sigma.ι F i ≫ eF.hom = TopCat.sigmaι F i :=
          TopCat.sigmaIsoSigma_hom_ι F i
        calc
          φ i ≫ Sigma.ι G i = TopCat.sigmaι F i ≫ m ≫ eG.inv := by
            apply TopCat.ext
            intro x
            calc
              (φ i ≫ Sigma.ι G i) x = (Sigma.ι G i) ((φ i) x) := by
                simp only [TopCat.hom_comp, ContinuousMap.comp_apply]
              _ = eG.inv ⟨i, (φ i) x⟩ := by
                rw [← TopCat.sigmaIsoSigma_inv_apply (α := G) i ((φ i) x)]
              _ = eG.inv (m ⟨i, x⟩) := by
                rw [← h_m_apply i x]
              _ = eG.inv (m ((TopCat.sigmaι F i) x)) := by
                rw [← h_sigmaι_apply i x]
              _ = (TopCat.sigmaι F i ≫ m ≫ eG.inv) x := by
                simp only [TopCat.hom_comp, ContinuousMap.comp_apply]
          _ = (Sigma.ι F i ≫ eF.hom) ≫ m ≫ eG.inv := by rw [hι]
          _ = Sigma.ι F i ≫ (eF.hom ≫ m ≫ eG.inv) := by
            simp only [Category.assoc]
  have h_inner : IsEmbedding (⇑m ∘ ⇑eF.hom) :=
    IsEmbedding.comp h_emb_m h_emb_eF
  have h_comp : IsEmbedding (⇑eG.inv ∘ (⇑m ∘ ⇑eF.hom)) :=
    IsEmbedding.comp h_emb_eG_inv h_inner
  have h_cont_comp : Continuous (⇑eG.inv ∘ (⇑m ∘ ⇑eF.hom)) :=
    eG.inv.hom.continuous_toFun.comp
      (m.hom.continuous_toFun.comp eF.hom.hom.continuous_toFun)
  have h_comp' : IsEmbedding (eF.hom ≫ m ≫ eG.inv) := by
    have heq : (eF.hom ≫ m ≫ eG.inv : (∐ F) ⟶ (∐ G)) =
        TopCat.ofHom ⟨⇑eG.inv ∘ (⇑m ∘ ⇑eF.hom), h_cont_comp⟩ := rfl
    rw [heq]
    exact h_comp
  rw [h_eq]
  exact h_comp'

end TopCat
