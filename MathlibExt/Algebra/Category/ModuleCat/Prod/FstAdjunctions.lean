/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.Prod.EmbeddingComponents

/-!
# First-factor adjunctions for product modules

Adjunctions between `ModuleCat.prodEmbeddingFst` and `eComponentFunctor`:
`prodEmbeddingFst R S ⊣ eComponentFunctor` and
`eComponentFunctor ⊣ prodEmbeddingFst R S`, with accompanying
`IsLeftAdjoint` / `IsRightAdjoint` instances. The `e`-submodule
inclusion/projection transformations, the four unit/counit transformations,
the two adjunctions, and the instances are public construction data.
-/

@[expose] public section

open CategoryTheory

universe v uR uS

namespace ProdIdempotent

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

section UnitCounitFst

/-- Let `R` and `S` be rings and let `e = (1, 0)` in `R × S`. In `ModuleCat (R × S)`, this
natural transformation from the `e`-submodule functor to the identity
has component the inclusion `eM ⟶ M`. -/
noncomputable def eSubmoduleFunctorIncl :
    eSubmoduleFunctor (R := R) (S := S) ⟶ 𝟭 (ModuleCat.{v} (R × S)) where
  app M := ModuleCat.ofHom (eIncl (R := R) (S := S) (M := M))
  naturality X Y f := by
    apply ModuleCat.hom_ext
    exact (map_comp_eIncl (R := R) (S := S) (f := f.hom)).symm

/-- Let `R` and `S` be rings and let `e = (1, 0)` in `R × S`. In `ModuleCat (R × S)`, this
natural transformation from the identity to the `e`-submodule functor
has component `M ⟶ eM`, sending `m` to `e • m`. -/
noncomputable def eSubmoduleFunctorProj :
    𝟭 (ModuleCat.{v} (R × S)) ⟶ eSubmoduleFunctor (R := R) (S := S) where
  app M := ModuleCat.ofHom (eProj (R := R) (S := S) (M := M))
  naturality X Y f := by
    apply ModuleCat.hom_ext
    exact eProj_comp_map (R := R) (S := S) (f := f.hom)

/-- Let `R` and `S` be rings and let `e = (1, 0)` in `R × S`.
The unit for `prodEmbeddingFst R S ⊣ eComponentFunctor` is
`𝟭 (ModuleCat R) ⟶ prodEmbeddingFst R S ⋙ eComponentFunctor`.
On a `R`-module it identifies it with the whole `e`-component
of its embedded module, by the inverse of the forgetful-coordinate identification. -/
noncomputable def prodEmbeddingFst_eComponentFunctor_unit :
    𝟭 (ModuleCat.{v} R) ⟶ ModuleCat.prodEmbeddingFst R S ⋙ eComponentFunctor (R := R) (S := S) :=
  eComponentEmbeddingFstNatIso (R := R) (S := S).symm.hom

/-- Let `R` and `S` be rings and let `e = (1, 0)` in `R × S`.
The counit for `prodEmbeddingFst R S ⊣ eComponentFunctor` is
`eComponentFunctor ⋙ prodEmbeddingFst R S ⟶ 𝟭 (ModuleCat (R × S))`.
It identifies the embedded `e`-component with the submodule `eM`
and then includes that submodule into `M`. -/
noncomputable def prodEmbeddingFst_eComponentFunctor_counit :
    eComponentFunctor (R := R) (S := S) ⋙ ModuleCat.prodEmbeddingFst R S ⟶
      𝟭 (ModuleCat.{v} (R × S)) :=
  eSubmoduleNatIsoEmbeddingFst (R := R) (S := S).symm.hom ≫ eSubmoduleFunctorIncl

/-- Let `R` and `S` be rings and let `e = (1, 0)` in `R × S`.
The unit for `eComponentFunctor ⊣ prodEmbeddingFst R S` is
`𝟭 (ModuleCat (R × S)) ⟶ eComponentFunctor ⋙ prodEmbeddingFst R S`.
It projects `m` to `e • m` in `eM` and then uses the identification
with the embedded component. -/
noncomputable def eComponentFunctor_prodEmbeddingFst_unit :
    𝟭 (ModuleCat.{v} (R × S)) ⟶
      eComponentFunctor (R := R) (S := S) ⋙ ModuleCat.prodEmbeddingFst R S :=
  eSubmoduleFunctorProj ≫ eSubmoduleNatIsoEmbeddingFst (R := R) (S := S).hom

/-- Let `R` and `S` be rings and let `e = (1, 0)` in `R × S`.
The counit for `eComponentFunctor ⊣ prodEmbeddingFst R S` is
`prodEmbeddingFst R S ⋙ eComponentFunctor ⟶ 𝟭 (ModuleCat R)`.
It takes the `e`-component of an embedded `R`-module back to
that module by taking the underlying coordinate. -/
noncomputable def eComponentFunctor_prodEmbeddingFst_counit :
    ModuleCat.prodEmbeddingFst R S ⋙ eComponentFunctor (R := R) (S := S) ⟶
      𝟭 (ModuleCat.{v} R) :=
  eComponentEmbeddingFstNatIso (R := R) (S := S).hom

end UnitCounitFst

section AdjunctionFst

variable (R : Type uR) (S : Type uS) [Ring R] [Ring S]

/-- Let `R` and `S` be rings and let `e = (1, 0)` in `R × S`.
The first-factor embedding `prodEmbeddingFst R S` sends
`R`-modules to `(R × S)`-modules by restriction along `fst`; on the
embedded module `(r, s)` acts by `r`. The component functor `eComponentFunctor`
sends an `(R × S)`-module `M` to `eM` as a `R`-module. The embedding
is left adjoint to the component functor. -/
noncomputable def prodEmbeddingFstAdj_eComponentFunctor :
    ModuleCat.prodEmbeddingFst (R := R) (S := S) ⊣
      eComponentFunctor (R := R) (S := S) :=
  Adjunction.mkOfUnitCounit
    { unit := prodEmbeddingFst_eComponentFunctor_unit (R := R) (S := S)
      counit := prodEmbeddingFst_eComponentFunctor_counit (R := R) (S := S)
      left_triangle := by
        have h_assoc :
            Functor.whiskerRight
              (prodEmbeddingFst_eComponentFunctor_unit (R := R) (S := S))
              (ModuleCat.prodEmbeddingFst R S) ≫
              (Functor.associator _ _ _).hom =
            Functor.whiskerRight
              (prodEmbeddingFst_eComponentFunctor_unit (R := R) (S := S))
              (ModuleCat.prodEmbeddingFst R S) := by
          ext N
          simp only [NatTrans.comp_app, Functor.whiskerRight_app,
            Functor.associator_hom_app, Category.comp_id]
        calc
          Functor.whiskerRight
                (prodEmbeddingFst_eComponentFunctor_unit (R := R) (S := S))
                (ModuleCat.prodEmbeddingFst R S) ≫
              (Functor.associator _ _ _).hom ≫
              Functor.whiskerLeft (ModuleCat.prodEmbeddingFst R S)
                (prodEmbeddingFst_eComponentFunctor_counit (R := R) (S := S))
            = Functor.whiskerRight
                  (prodEmbeddingFst_eComponentFunctor_unit (R := R) (S := S))
                  (ModuleCat.prodEmbeddingFst R S) ≫
                Functor.whiskerLeft (ModuleCat.prodEmbeddingFst R S)
                  (prodEmbeddingFst_eComponentFunctor_counit (R := R) (S := S)) := by
              rw [← Category.assoc, h_assoc]
          _ = 𝟙 _ := by
              ext N x
              simp only [prodEmbeddingFst_eComponentFunctor_unit,
                prodEmbeddingFst_eComponentFunctor_counit, eSubmoduleFunctorIncl,
                eSubmoduleNatIsoEmbeddingFst, eSubmoduleIsoEmbeddingFst,
                eComponentEmbeddingFstNatIso, prodEmbeddingFst_eComponentIso,
                Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app]
              rfl
      right_triangle := by
        have h_assoc :
            Functor.whiskerLeft (eComponentFunctor (R := R) (S := S))
              (prodEmbeddingFst_eComponentFunctor_unit (R := R) (S := S)) ≫
              (Functor.associator _ _ _).inv =
            Functor.whiskerLeft (eComponentFunctor (R := R) (S := S))
              (prodEmbeddingFst_eComponentFunctor_unit (R := R) (S := S)) := by
          ext M
          simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
            Functor.associator_inv_app, Category.comp_id]
        calc
          Functor.whiskerLeft (eComponentFunctor (R := R) (S := S))
                (prodEmbeddingFst_eComponentFunctor_unit (R := R) (S := S)) ≫
              (Functor.associator _ _ _).inv ≫
              Functor.whiskerRight
                (prodEmbeddingFst_eComponentFunctor_counit (R := R) (S := S))
                (eComponentFunctor (R := R) (S := S))
            = Functor.whiskerLeft (eComponentFunctor (R := R) (S := S))
                  (prodEmbeddingFst_eComponentFunctor_unit (R := R) (S := S)) ≫
                Functor.whiskerRight
                  (prodEmbeddingFst_eComponentFunctor_counit (R := R) (S := S))
                  (eComponentFunctor (R := R) (S := S)) := by
              rw [← Category.assoc, h_assoc]
          _ = 𝟙 _ := by
              ext M x
              simp only [prodEmbeddingFst_eComponentFunctor_unit,
                prodEmbeddingFst_eComponentFunctor_counit, eSubmoduleFunctorIncl,
                eSubmoduleNatIsoEmbeddingFst, eSubmoduleIsoEmbeddingFst,
                eComponentEmbeddingFstNatIso, prodEmbeddingFst_eComponentIso,
                Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app]
              apply Subtype.ext
              rfl
    }

/-- Let `R` and `S` be rings and let `e = (1, 0)` in `R × S`.
The first-factor embedding `prodEmbeddingFst R S` sends
`R`-modules to `(R × S)`-modules by restriction along `fst`; on the
embedded module `(r, s)` acts by `r`. The component functor `eComponentFunctor`
sends an `(R × S)`-module `M` to `eM` as a `R`-module. The component functor
is left adjoint to the embedding. -/
noncomputable def eComponentFunctorAdj_prodEmbeddingFst :
    eComponentFunctor (R := R) (S := S) ⊣
      ModuleCat.prodEmbeddingFst (R := R) (S := S) :=
  Adjunction.mkOfUnitCounit
    { unit := eComponentFunctor_prodEmbeddingFst_unit (R := R) (S := S)
      counit := eComponentFunctor_prodEmbeddingFst_counit (R := R) (S := S)
      left_triangle := by
        have h_assoc :
            Functor.whiskerRight
              (eComponentFunctor_prodEmbeddingFst_unit (R := R) (S := S))
              (eComponentFunctor (R := R) (S := S)) ≫
              (Functor.associator _ _ _).hom =
            Functor.whiskerRight
              (eComponentFunctor_prodEmbeddingFst_unit (R := R) (S := S))
              (eComponentFunctor (R := R) (S := S)) := by
          ext M
          simp only [NatTrans.comp_app, Functor.whiskerRight_app,
            Functor.associator_hom_app, Category.comp_id]
        calc
          Functor.whiskerRight
                (eComponentFunctor_prodEmbeddingFst_unit (R := R) (S := S))
                (eComponentFunctor (R := R) (S := S)) ≫
              (Functor.associator _ _ _).hom ≫
              Functor.whiskerLeft (eComponentFunctor (R := R) (S := S))
                (eComponentFunctor_prodEmbeddingFst_counit (R := R) (S := S))
            = Functor.whiskerRight
                  (eComponentFunctor_prodEmbeddingFst_unit (R := R) (S := S))
                  (eComponentFunctor (R := R) (S := S)) ≫
                Functor.whiskerLeft (eComponentFunctor (R := R) (S := S))
                  (eComponentFunctor_prodEmbeddingFst_counit (R := R) (S := S)) := by
              rw [← Category.assoc, h_assoc]
          _ = 𝟙 _ := by
              ext M x
              have hx : x.val ∈ eSubmodule (R := R) (S := S) (M := M) := x.2
              have he : e R S • x.val = x.val := e_smul_of_mem_eSubmodule hx
              simp only [eComponentFunctor_prodEmbeddingFst_unit,
                eComponentFunctor_prodEmbeddingFst_counit, eSubmoduleFunctorProj,
                eSubmoduleNatIsoEmbeddingFst, eSubmoduleIsoEmbeddingFst,
                eComponentEmbeddingFstNatIso, prodEmbeddingFst_eComponentIso,
                Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
                eProj]
              apply Subtype.ext
              exact he
      right_triangle := by
        have h_assoc :
            Functor.whiskerLeft (ModuleCat.prodEmbeddingFst R S)
              (eComponentFunctor_prodEmbeddingFst_unit (R := R) (S := S)) ≫
              (Functor.associator _ _ _).inv =
            Functor.whiskerLeft (ModuleCat.prodEmbeddingFst R S)
              (eComponentFunctor_prodEmbeddingFst_unit (R := R) (S := S)) := by
          ext N
          simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
            Functor.associator_inv_app, Category.comp_id]
        calc
          Functor.whiskerLeft (ModuleCat.prodEmbeddingFst R S)
                (eComponentFunctor_prodEmbeddingFst_unit (R := R) (S := S)) ≫
              (Functor.associator _ _ _).inv ≫
              Functor.whiskerRight
                (eComponentFunctor_prodEmbeddingFst_counit (R := R) (S := S))
                (ModuleCat.prodEmbeddingFst R S)
            = Functor.whiskerLeft (ModuleCat.prodEmbeddingFst R S)
                  (eComponentFunctor_prodEmbeddingFst_unit (R := R) (S := S)) ≫
                Functor.whiskerRight
                  (eComponentFunctor_prodEmbeddingFst_counit (R := R) (S := S))
                  (ModuleCat.prodEmbeddingFst R S) := by
              rw [← Category.assoc, h_assoc]
          _ = 𝟙 _ := by
              ext N x
              have hx_top : x ∈ eSubmodule (R := R) (S := S)
                  (M := (ModuleCat.prodEmbeddingFst R S).obj N) := by
                rw [eSubmodule_prodEmbeddingFst_eq_top N]
                trivial
              have he : e R S • x = x := by
                rw [mem_eSubmodule_iff] at hx_top
                exact hx_top
              calc
                ((Functor.whiskerLeft (ModuleCat.prodEmbeddingFst R S)
                      (eComponentFunctor_prodEmbeddingFst_unit (R := R) (S := S)) ≫
                    Functor.whiskerRight
                      (eComponentFunctor_prodEmbeddingFst_counit (R := R) (S := S))
                      (ModuleCat.prodEmbeddingFst R S)).app N) x
                  = e R S • x := by
                    dsimp only [eComponentFunctor_prodEmbeddingFst_unit,
                      eComponentFunctor_prodEmbeddingFst_counit,
                      eSubmoduleFunctorProj, eSubmoduleNatIsoEmbeddingFst,
                      eSubmoduleIsoEmbeddingFst, eComponentEmbeddingFstNatIso,
                      prodEmbeddingFst_eComponentIso, eProj,
                      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app]
                    rfl
                _ = x := he
    }

/-- `prodEmbeddingFst` is left adjoint to `eComponentFunctor`. -/
instance isLeftAdjoint_prodEmbeddingFst :
    (ModuleCat.prodEmbeddingFst (R := R) (S := S)).IsLeftAdjoint where
  exists_rightAdjoint :=
    ⟨eComponentFunctor (R := R) (S := S),
      ⟨prodEmbeddingFstAdj_eComponentFunctor R S⟩⟩

/-- `eComponentFunctor` is right adjoint to `prodEmbeddingFst`. -/
instance isRightAdjoint_eComponentFunctor_of_prodEmbeddingFst_left :
    (eComponentFunctor (R := R) (S := S)).IsRightAdjoint where
  exists_leftAdjoint :=
    ⟨ModuleCat.prodEmbeddingFst (R := R) (S := S),
      ⟨prodEmbeddingFstAdj_eComponentFunctor R S⟩⟩

/-- `eComponentFunctor` is left adjoint to `prodEmbeddingFst`. -/
instance isLeftAdjoint_eComponentFunctor :
    (eComponentFunctor (R := R) (S := S)).IsLeftAdjoint where
  exists_rightAdjoint :=
    ⟨ModuleCat.prodEmbeddingFst (R := R) (S := S),
      ⟨eComponentFunctorAdj_prodEmbeddingFst R S⟩⟩

/-- `prodEmbeddingFst` is right adjoint to `eComponentFunctor`. -/
instance isRightAdjoint_prodEmbeddingFst_of_eComponent_left :
    (ModuleCat.prodEmbeddingFst (R := R) (S := S)).IsRightAdjoint where
  exists_leftAdjoint :=
    ⟨eComponentFunctor (R := R) (S := S),
      ⟨eComponentFunctorAdj_prodEmbeddingFst R S⟩⟩

end AdjunctionFst

end ProdIdempotent
