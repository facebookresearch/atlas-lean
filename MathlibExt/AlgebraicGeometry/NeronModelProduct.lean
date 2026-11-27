/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NeronModelUniqueness

/-!
# Néron model of a product

If `M` and `N` are Néron models over `R` of `K`-schemes `A` and `B`, then the fibre product
`M.model ×_R N.model`, with the identification of its generic fibre with `A ×_K B` induced by
the two given identifications, is a Néron model of `A ×_K B` (`NeronModel.prod`). Finite type
is kept (`FiniteTypeNeronModel.prod`).

Reference: B. Conrad, *Semistable reduction for abelian varieties*, seminar notes, Stanford,
2011, http://math.stanford.edu/~conrad/mordellsem/Notes/L13.pdf: §4, proof of
Proposition 4.3, p. 9 ("Néron models commute with products"); S. Lichtenstein, *Néron models*,
seminar notes, Stanford, 2011, http://math.stanford.edu/~conrad/mordellsem/Notes/L11.pdf:
Proposition 1.4.2 (ii), p. 5.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NeronModels

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.SemistableModels

universe u

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  {A B : Over (Spec (.of K))}

/-- The structure morphism of a binary product of schemes over `Spec R` factors through the
first projection of the fibre product. -/
theorem prod_hom_eq (X Y : Over (trait R)) :
    (X ⨯ Y).hom = (Over.prodLeftIsoPullback X Y).hom ≫ pullback.fst X.hom Y.hom ≫ X.hom := by
  rw [← Over.w (prod.fst : X ⨯ Y ⟶ X), ← Over.prodLeftIsoPullback_hom_fst, Category.assoc]

/-- Products of smooth schemes over `Spec R` are smooth. -/
instance (X Y : Over (trait R)) [Smooth X.hom] [Smooth Y.hom] : Smooth (X ⨯ Y).hom := by
  rw [prod_hom_eq]; infer_instance
/-- Products of separated schemes over `Spec R` are separated. -/
instance (X Y : Over (trait R)) [IsSeparated X.hom] [IsSeparated Y.hom] :
    IsSeparated (X ⨯ Y).hom := by
  rw [prod_hom_eq]; infer_instance
/-- Products of schemes locally of finite type over `Spec R` are locally of finite type. -/
instance (X Y : Over (trait R)) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType (X ⨯ Y).hom := by
  rw [prod_hom_eq]; infer_instance
/-- Products of quasi-compact schemes over `Spec R` are quasi-compact. -/
instance (X Y : Over (trait R)) [QuasiCompact X.hom] [QuasiCompact Y.hom] :
    QuasiCompact (X ⨯ Y).hom := by
  rw [prod_hom_eq]; infer_instance

namespace NeronModel

/-- **Néron model of a product.** If `M` and `N` are Néron models over `R` of the `K`-schemes
`A` and `B`, then `M.model ⨯ N.model` (the fibre product over `Spec R`), with the identification
of its generic fibre with `A ⨯ B` induced by `M.genericIso` and `N.genericIso`, is a Néron model
of `A ⨯ B`.

This is the fact "Néron models commute with products" used in Conrad, *Semistable reduction
for abelian varieties*, proof of Proposition 4.3, p. 9 (Lichtenstein, *Néron models*,
Proposition 1.4.2 (ii), p. 5), for any domain `R` with fraction field `K` and any `K`-schemes
`A` and `B`. -/
def prod (M : NeronModel R K A) (N : NeronModel R K B) : NeronModel R K (A ⨯ B) :=
  ofBijective (M.model ⨯ N.model)
    (PreservesLimitPair.iso (genericFunctor R K) M.model N.model ≪≫
      prod.mapIso M.genericIso N.genericIso)
    (fun Y _ ↦ by
      refine ⟨fun e₁ e₂ h ↦ ?_, fun f ↦ ?_⟩
      · simp only at h
        apply prod.hom_ext
        · apply (M.bijective_map Y).1
          simp only [Functor.map_comp, h]
        · apply (N.bijective_map Y).1
          simp only [Functor.map_comp, h]
      · obtain ⟨a, ha⟩ := (M.bijective_map Y).2 (f ≫ (genericFunctor R K).map prod.fst)
        obtain ⟨b, hb⟩ := (N.bijective_map Y).2 (f ≫ (genericFunctor R K).map prod.snd)
        simp only at ha hb ⊢
        refine ⟨prod.lift a b, ?_⟩
        rw [← cancel_mono (PreservesLimitPair.iso (genericFunctor R K) M.model N.model).hom]
        apply prod.hom_ext <;>
          simp [PreservesLimitPair.iso_hom, ← Functor.map_comp, ha, hb])

/-- The model of the product Néron model is the product of the models. -/
@[simp] theorem prod_model (M : NeronModel R K A) (N : NeronModel R K B) :
    (M.prod N).model = (M.model ⨯ N.model) := rfl

/-- The identification of the generic fibre of the product Néron model is the one induced by
the identifications of the factors. -/
theorem prod_genericIso (M : NeronModel R K A) (N : NeronModel R K B) :
    (M.prod N).genericIso =
      PreservesLimitPair.iso (genericFunctor R K) M.model N.model ≪≫
        prod.mapIso M.genericIso N.genericIso := rfl

end NeronModel

/-- The product of two finite-type Néron models is a finite-type Néron model of the product. -/
def FiniteTypeNeronModel.prod (M : FiniteTypeNeronModel R K A) (N : FiniteTypeNeronModel R K B) :
    FiniteTypeNeronModel R K (A ⨯ B) where
  toNeronModel := M.toNeronModel.prod N.toNeronModel
  quasiCompact := inferInstanceAs (QuasiCompact (M.model ⨯ N.model).hom)

end MathlibExt.AlgebraicGeometry.NeronModels
