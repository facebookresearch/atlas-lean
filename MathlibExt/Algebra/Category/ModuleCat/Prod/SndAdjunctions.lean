/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.Prod.EmbeddingComponents

/-!
# Second-factor adjunctions for product rings

For `R × S` this module shows that the second-factor embedding
`ModuleCat.prodEmbeddingSnd R S : ModuleCat S ⥤ ModuleCat (R × S)` and the
second-factor component functor `fComponentFunctor` are adjoint in both
orientations. The `f = (0,1)` submodule gives natural isos identifying the
`f`-component after embedding with the identity and the ambient `f`-submodule
functor with `fComponentFunctor ⋙ prodEmbeddingSnd`. Inclusion and projection
of the `f`-submodule supply the remaining side of each (co)unit. The
inclusion/projection transformations, the four unit/counit transformations,
the two adjunctions, and the `IsLeftAdjoint` / `IsRightAdjoint` instances are
public construction data.
-/

@[expose] public section

open CategoryTheory

universe v uR uS

namespace ProdIdempotent

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

section UnitCounitSnd

/-- Inclusion of the `f`-submodule into the ambient `(R×S)`-module as a natural transformation. -/
noncomputable def fSubmoduleFunctorIncl :
    fSubmoduleFunctor (R := R) (S := S) ⟶ 𝟭 (ModuleCat.{v} (R × S)) where
  app M := ModuleCat.ofHom (fIncl (R := R) (S := S) (M := M))
  naturality X Y f := by
    apply ModuleCat.hom_ext
    exact (map_comp_fIncl (R := R) (S := S) (f := f.hom)).symm

/-- Projection onto the `f`-submodule as a natural transformation from identity. -/
noncomputable def fSubmoduleFunctorProj :
    𝟭 (ModuleCat.{v} (R × S)) ⟶ fSubmoduleFunctor (R := R) (S := S) where
  app M := ModuleCat.ofHom (fProj (R := R) (S := S) (M := M))
  naturality X Y f := by
    apply ModuleCat.hom_ext
    exact fProj_comp_map (R := R) (S := S) (f := f.hom)

/-- Unit for `prodEmbeddingSnd ⊣ fComponentFunctor`. -/
noncomputable def prodEmbeddingSnd_fComponentFunctor_unit :
    𝟭 (ModuleCat.{v} S) ⟶ ModuleCat.prodEmbeddingSnd R S ⋙ fComponentFunctor (R := R) (S := S) :=
  fComponentEmbeddingSndNatIso (R := R) (S := S).symm.hom

/-- Counit for `prodEmbeddingSnd ⊣ fComponentFunctor`. -/
noncomputable def prodEmbeddingSnd_fComponentFunctor_counit :
    fComponentFunctor (R := R) (S := S) ⋙ ModuleCat.prodEmbeddingSnd R S ⟶
      𝟭 (ModuleCat.{v} (R × S)) :=
  fSubmoduleNatIsoEmbeddingSnd (R := R) (S := S).symm.hom ≫ fSubmoduleFunctorIncl

/-- Unit for `fComponentFunctor ⊣ prodEmbeddingSnd`. -/
noncomputable def fComponentFunctor_prodEmbeddingSnd_unit :
    𝟭 (ModuleCat.{v} (R × S)) ⟶
      fComponentFunctor (R := R) (S := S) ⋙ ModuleCat.prodEmbeddingSnd R S :=
  fSubmoduleFunctorProj ≫ fSubmoduleNatIsoEmbeddingSnd (R := R) (S := S).hom

/-- Counit for `fComponentFunctor ⊣ prodEmbeddingSnd`. -/
noncomputable def fComponentFunctor_prodEmbeddingSnd_counit :
    ModuleCat.prodEmbeddingSnd R S ⋙ fComponentFunctor (R := R) (S := S) ⟶
      𝟭 (ModuleCat.{v} S) :=
  fComponentEmbeddingSndNatIso (R := R) (S := S).hom

end UnitCounitSnd

section AdjunctionSnd

variable (R : Type uR) (S : Type uS) [Ring R] [Ring S]

/-- `prodEmbeddingSnd R S ⊣ fComponentFunctor` : embedding left adjoint to second projection. -/
noncomputable def prodEmbeddingSndAdj_fComponentFunctor :
    ModuleCat.prodEmbeddingSnd (R := R) (S := S) ⊣
      fComponentFunctor (R := R) (S := S) :=
  Adjunction.mkOfUnitCounit
    { unit := prodEmbeddingSnd_fComponentFunctor_unit (R := R) (S := S)
      counit := prodEmbeddingSnd_fComponentFunctor_counit (R := R) (S := S)
      left_triangle := by
        have h_assoc :
            Functor.whiskerRight
              (prodEmbeddingSnd_fComponentFunctor_unit (R := R) (S := S))
              (ModuleCat.prodEmbeddingSnd R S) ≫
              (Functor.associator _ _ _).hom =
            Functor.whiskerRight
              (prodEmbeddingSnd_fComponentFunctor_unit (R := R) (S := S))
              (ModuleCat.prodEmbeddingSnd R S) := by
          ext N
          simp only [NatTrans.comp_app, Functor.whiskerRight_app,
            Functor.associator_hom_app, Category.comp_id]
        calc
          Functor.whiskerRight
                (prodEmbeddingSnd_fComponentFunctor_unit (R := R) (S := S))
                (ModuleCat.prodEmbeddingSnd R S) ≫
              (Functor.associator _ _ _).hom ≫
              Functor.whiskerLeft (ModuleCat.prodEmbeddingSnd R S)
                (prodEmbeddingSnd_fComponentFunctor_counit (R := R) (S := S))
            = Functor.whiskerRight
                  (prodEmbeddingSnd_fComponentFunctor_unit (R := R) (S := S))
                  (ModuleCat.prodEmbeddingSnd R S) ≫
                Functor.whiskerLeft (ModuleCat.prodEmbeddingSnd R S)
                  (prodEmbeddingSnd_fComponentFunctor_counit (R := R) (S := S)) := by
              rw [← Category.assoc, h_assoc]
          _ = 𝟙 _ := by
              ext N x
              simp only [prodEmbeddingSnd_fComponentFunctor_unit,
                prodEmbeddingSnd_fComponentFunctor_counit, fSubmoduleFunctorIncl,
                fSubmoduleNatIsoEmbeddingSnd, fSubmoduleIsoEmbeddingSnd,
                fComponentEmbeddingSndNatIso, prodEmbeddingSnd_fComponentIso,
                Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app]
              rfl
      right_triangle := by
        have h_assoc :
            Functor.whiskerLeft (fComponentFunctor (R := R) (S := S))
              (prodEmbeddingSnd_fComponentFunctor_unit (R := R) (S := S)) ≫
              (Functor.associator _ _ _).inv =
            Functor.whiskerLeft (fComponentFunctor (R := R) (S := S))
              (prodEmbeddingSnd_fComponentFunctor_unit (R := R) (S := S)) := by
          ext M
          simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
            Functor.associator_inv_app, Category.comp_id]
        calc
          Functor.whiskerLeft (fComponentFunctor (R := R) (S := S))
                (prodEmbeddingSnd_fComponentFunctor_unit (R := R) (S := S)) ≫
              (Functor.associator _ _ _).inv ≫
              Functor.whiskerRight
                (prodEmbeddingSnd_fComponentFunctor_counit (R := R) (S := S))
                (fComponentFunctor (R := R) (S := S))
            = Functor.whiskerLeft (fComponentFunctor (R := R) (S := S))
                  (prodEmbeddingSnd_fComponentFunctor_unit (R := R) (S := S)) ≫
                Functor.whiskerRight
                  (prodEmbeddingSnd_fComponentFunctor_counit (R := R) (S := S))
                  (fComponentFunctor (R := R) (S := S)) := by
              rw [← Category.assoc, h_assoc]
          _ = 𝟙 _ := by
              ext M x
              simp only [prodEmbeddingSnd_fComponentFunctor_unit,
                prodEmbeddingSnd_fComponentFunctor_counit, fSubmoduleFunctorIncl,
                fSubmoduleNatIsoEmbeddingSnd, fSubmoduleIsoEmbeddingSnd,
                fComponentEmbeddingSndNatIso, prodEmbeddingSnd_fComponentIso,
                Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app]
              apply Subtype.ext
              rfl
    }

/-- `fComponentFunctor ⊣ prodEmbeddingSnd R S` : second projection left adjoint to embedding. -/
noncomputable def fComponentFunctorAdj_prodEmbeddingSnd :
    fComponentFunctor (R := R) (S := S) ⊣
      ModuleCat.prodEmbeddingSnd (R := R) (S := S) :=
  Adjunction.mkOfUnitCounit
    { unit := fComponentFunctor_prodEmbeddingSnd_unit (R := R) (S := S)
      counit := fComponentFunctor_prodEmbeddingSnd_counit (R := R) (S := S)
      left_triangle := by
        have h_assoc :
            Functor.whiskerRight
              (fComponentFunctor_prodEmbeddingSnd_unit (R := R) (S := S))
              (fComponentFunctor (R := R) (S := S)) ≫
              (Functor.associator _ _ _).hom =
            Functor.whiskerRight
              (fComponentFunctor_prodEmbeddingSnd_unit (R := R) (S := S))
              (fComponentFunctor (R := R) (S := S)) := by
          ext M
          simp only [NatTrans.comp_app, Functor.whiskerRight_app,
            Functor.associator_hom_app, Category.comp_id]
        calc
          Functor.whiskerRight
                (fComponentFunctor_prodEmbeddingSnd_unit (R := R) (S := S))
                (fComponentFunctor (R := R) (S := S)) ≫
              (Functor.associator _ _ _).hom ≫
              Functor.whiskerLeft (fComponentFunctor (R := R) (S := S))
                (fComponentFunctor_prodEmbeddingSnd_counit (R := R) (S := S))
            = Functor.whiskerRight
                  (fComponentFunctor_prodEmbeddingSnd_unit (R := R) (S := S))
                  (fComponentFunctor (R := R) (S := S)) ≫
                Functor.whiskerLeft (fComponentFunctor (R := R) (S := S))
                  (fComponentFunctor_prodEmbeddingSnd_counit (R := R) (S := S)) := by
              rw [← Category.assoc, h_assoc]
          _ = 𝟙 _ := by
              ext M x
              have hx : x.val ∈ fSubmodule (R := R) (S := S) (M := M) := x.2
              have hf : f R S • x.val = x.val := f_smul_of_mem_fSubmodule hx
              simp only [fComponentFunctor_prodEmbeddingSnd_unit,
                fComponentFunctor_prodEmbeddingSnd_counit, fSubmoduleFunctorProj,
                fSubmoduleNatIsoEmbeddingSnd, fSubmoduleIsoEmbeddingSnd,
                fComponentEmbeddingSndNatIso, prodEmbeddingSnd_fComponentIso,
                Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
                fProj]
              apply Subtype.ext
              exact hf
      right_triangle := by
        have h_assoc :
            Functor.whiskerLeft (ModuleCat.prodEmbeddingSnd R S)
              (fComponentFunctor_prodEmbeddingSnd_unit (R := R) (S := S)) ≫
              (Functor.associator _ _ _).inv =
            Functor.whiskerLeft (ModuleCat.prodEmbeddingSnd R S)
              (fComponentFunctor_prodEmbeddingSnd_unit (R := R) (S := S)) := by
          ext N
          simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
            Functor.associator_inv_app, Category.comp_id]
        calc
          Functor.whiskerLeft (ModuleCat.prodEmbeddingSnd R S)
                (fComponentFunctor_prodEmbeddingSnd_unit (R := R) (S := S)) ≫
              (Functor.associator _ _ _).inv ≫
              Functor.whiskerRight
                (fComponentFunctor_prodEmbeddingSnd_counit (R := R) (S := S))
                (ModuleCat.prodEmbeddingSnd R S)
            = Functor.whiskerLeft (ModuleCat.prodEmbeddingSnd R S)
                  (fComponentFunctor_prodEmbeddingSnd_unit (R := R) (S := S)) ≫
                Functor.whiskerRight
                  (fComponentFunctor_prodEmbeddingSnd_counit (R := R) (S := S))
                  (ModuleCat.prodEmbeddingSnd R S) := by
              rw [← Category.assoc, h_assoc]
          _ = 𝟙 _ := by
              ext N x
              have hx_top : x ∈ fSubmodule (R := R) (S := S)
                  (M := (ModuleCat.prodEmbeddingSnd R S).obj N) := by
                rw [fSubmodule_prodEmbeddingSnd_eq_top N]
                trivial
              have hf : f R S • x = x := by
                rw [mem_fSubmodule_iff] at hx_top
                exact hx_top
              calc
                ((Functor.whiskerLeft (ModuleCat.prodEmbeddingSnd R S)
                      (fComponentFunctor_prodEmbeddingSnd_unit (R := R) (S := S)) ≫
                    Functor.whiskerRight
                      (fComponentFunctor_prodEmbeddingSnd_counit (R := R) (S := S))
                      (ModuleCat.prodEmbeddingSnd R S)).app N) x
                  = f R S • x := by
                    dsimp only [fComponentFunctor_prodEmbeddingSnd_unit,
                      fComponentFunctor_prodEmbeddingSnd_counit,
                      fSubmoduleFunctorProj, fSubmoduleNatIsoEmbeddingSnd,
                      fSubmoduleIsoEmbeddingSnd, fComponentEmbeddingSndNatIso,
                      prodEmbeddingSnd_fComponentIso, fProj,
                      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app]
                    rfl
                _ = x := hf
    }

/-- `prodEmbeddingSnd` is a left adjoint; its right adjoint is `fComponentFunctor`. -/
instance isLeftAdjoint_prodEmbeddingSnd :
    (ModuleCat.prodEmbeddingSnd (R := R) (S := S)).IsLeftAdjoint where
  exists_rightAdjoint :=
    ⟨fComponentFunctor (R := R) (S := S),
      ⟨prodEmbeddingSndAdj_fComponentFunctor R S⟩⟩

/-- `fComponentFunctor` is right adjoint to `prodEmbeddingSnd` in the first orientation. -/
instance isRightAdjoint_fComponentFunctor_of_prodEmbeddingSnd_left :
    (fComponentFunctor (R := R) (S := S)).IsRightAdjoint where
  exists_leftAdjoint :=
    ⟨ModuleCat.prodEmbeddingSnd (R := R) (S := S),
      ⟨prodEmbeddingSndAdj_fComponentFunctor R S⟩⟩

/-- `fComponentFunctor` is left adjoint; its right adjoint is `prodEmbeddingSnd`. -/
instance isLeftAdjoint_fComponentFunctor :
    (fComponentFunctor (R := R) (S := S)).IsLeftAdjoint where
  exists_rightAdjoint :=
    ⟨ModuleCat.prodEmbeddingSnd (R := R) (S := S),
      ⟨fComponentFunctorAdj_prodEmbeddingSnd R S⟩⟩

/-- `prodEmbeddingSnd` is right adjoint to `fComponentFunctor` in the second orientation. -/
instance isRightAdjoint_prodEmbeddingSnd_of_fComponent_left :
    (ModuleCat.prodEmbeddingSnd (R := R) (S := S)).IsRightAdjoint where
  exists_leftAdjoint :=
    ⟨fComponentFunctor (R := R) (S := S),
      ⟨fComponentFunctorAdj_prodEmbeddingSnd R S⟩⟩

end AdjunctionSnd

end ProdIdempotent
