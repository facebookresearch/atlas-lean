/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SingularHomology.Integral
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.TopCatULiftSingularIso
public import MathlibExt.AlgebraicTopology.LocalCoefficient.HomotopyFiberAcyclicity
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.Topology.Category.TopCat.ULift

/-!
# Integral singular homology under an arbitrary carrier lift

Both the singular-simplex index and the integer coefficient carrier are
transported. The comparison uses the existing exact additive universe-lift
functor on abelian groups. It applies to an arbitrary original carrier,
rather than only to a space in universe zero.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v

namespace AlgebraicTopology.IntegralUniverseLift

private abbrev coefficientFunctor : AddCommGrpCat.{u} ⥤ AddCommGrpCat.{max u v} :=
  AddCommGrpCat.uliftFunctor.{v, u}

private abbrev originalCoefficients : AddCommGrpCat.{u} :=
  AlgebraicTopology.singularIntegralCoefficients.{u}

private abbrev liftedCoefficients : AddCommGrpCat.{max u v} :=
  AlgebraicTopology.singularIntegralCoefficients.{max u v}

private local instance originalCoproducts : HasCoproducts.{u} AddCommGrpCat.{u} :=
  fun I =>
    let : Small.{u} (Discrete I) := small_self (Discrete I)
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

private local instance liftedCoproducts :
    HasCoproducts.{max u v} AddCommGrpCat.{max u v} := fun I =>
  let : Small.{max u v} (Discrete I) := small_self (Discrete I)
  AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

private local instance originalIndexLiftedCoproducts :
    HasCoproducts.{u} AddCommGrpCat.{max u v} := fun I =>
  let : Small.{max u v} (Discrete I) :=
    small_of_injective
      (f := fun i : Discrete I => (ULift.up i : ULift.{v} (Discrete I)))
      ULift.up_injective
  AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

private def coefficientIso :
    liftedCoefficients.{u, v} ≅
      coefficientFunctor.{u, v}.obj originalCoefficients.{u} :=
  AddEquiv.toAddCommGrpIso
    { toFun := fun z => ULift.up (ULift.up z.down)
      invFun := fun z => ULift.up z.down.down
      left_inv := by intro z; cases z; rfl
      right_inv := by intro z; rcases z with ⟨⟨z⟩⟩; rfl
      map_add' := fun _ _ => rfl }

private abbrev originalComplex (X : SSet.{u}) :=
  X.chainComplex originalCoefficients.{u}

private abbrev liftedComplex (X : SSet.{u}) :=
  (SSet.uliftFunctor.{v, u}.obj X).chainComplex liftedCoefficients.{u, v}

private def degreeHom (X : SSet.{u}) (n : ℕ) :
    (liftedComplex.{u, v} X).X n ⟶
      coefficientFunctor.{u, v}.obj ((originalComplex X).X n) :=
  Sigma.desc (fun σ => coefficientIso.{u, v}.hom ≫
    coefficientFunctor.{u, v}.map (X.ιChainComplex (R := originalCoefficients) σ.down))

private def degreeInv (X : SSet.{u}) (n : ℕ) :
    coefficientFunctor.{u, v}.obj ((originalComplex X).X n) ⟶
      (liftedComplex.{u, v} X).X n :=
  inv (sigmaComparison coefficientFunctor.{u, v}
    (fun _ : X _⦋n⦌ => originalCoefficients.{u})) ≫
      Sigma.desc (fun σ => coefficientIso.{u, v}.inv ≫
        (SSet.uliftFunctor.{v, u}.obj X).ιChainComplex
          (R := liftedCoefficients.{u, v}) (ULift.up σ))

@[reassoc]
private theorem ι_degreeHom (X : SSet.{u}) (n : ℕ)
    (σ : (SSet.uliftFunctor.{v, u}.obj X) _⦋n⦌) :
    (SSet.uliftFunctor.{v, u}.obj X).ιChainComplex
        (R := liftedCoefficients.{u, v}) σ ≫ degreeHom.{u, v} X n =
      coefficientIso.{u, v}.hom ≫ coefficientFunctor.{u, v}.map
        (X.ιChainComplex (R := originalCoefficients.{u}) σ.down) := by
  dsimp only [degreeHom, SSet.ιChainComplex]
  exact Sigma.ι_comp_desc _ σ

@[reassoc]
private theorem map_ι_degreeInv (X : SSet.{u}) (n : ℕ) (σ : X _⦋n⦌) :
    coefficientFunctor.{u, v}.map
        (X.ιChainComplex (R := originalCoefficients.{u}) σ) ≫ degreeInv.{u, v} X n =
      coefficientIso.{u, v}.inv ≫
        (SSet.uliftFunctor.{v, u}.obj X).ιChainComplex
          (R := liftedCoefficients.{u, v}) (ULift.up σ) := by
  dsimp only [degreeInv, SSet.ιChainComplex]
  rw [← Category.assoc, map_ι_comp_inv_sigmaComparison, Sigma.ι_comp_desc]

private def degreeIso (X : SSet.{u}) (n : ℕ) :
    (liftedComplex.{u, v} X).X n ≅
      coefficientFunctor.{u, v}.obj ((originalComplex X).X n) where
  hom := degreeHom X n
  inv := degreeInv X n
  hom_inv_id := by
    apply SSet.chainComplex_hom_ext
    intro σ
    let L : SSet.{max u v} := SSet.uliftFunctor.{v, u}.obj X
    let F : AddCommGrpCat.{u} ⥤ AddCommGrpCat.{max u v} := coefficientFunctor.{u, v}
    let C := coefficientIso.{u, v}
    let s : L _⦋n⦌ := ULift.up σ.down
    let iσ : liftedCoefficients.{u, v} ⟶ (liftedComplex.{u, v} X).X n :=
      L.ιChainComplex (R := liftedCoefficients.{u, v}) σ
    let is : liftedCoefficients.{u, v} ⟶ (liftedComplex.{u, v} X).X n :=
      L.ιChainComplex (R := liftedCoefficients.{u, v}) s
    let i₀ : originalCoefficients.{u} ⟶ (originalComplex X).X n :=
      X.ιChainComplex (R := originalCoefficients.{u}) σ.down
    have hs : s = σ := ULift.up_down σ
    have hHom : iσ ≫ degreeHom.{u, v} X n = C.hom ≫ F.map i₀ :=
      ι_degreeHom.{u, v} X n σ
    have hInv : F.map i₀ ≫ degreeInv.{u, v} X n = C.inv ≫ is :=
      map_ι_degreeInv.{u, v} X n σ.down
    have hIndex : is = iσ :=
      congrArg (fun τ : L _⦋n⦌ => L.ιChainComplex (R := liftedCoefficients.{u, v}) τ) hs
    change iσ ≫ (degreeHom.{u, v} X n ≫ degreeInv.{u, v} X n) = iσ ≫ 𝟙 _
    calc
      iσ ≫ (degreeHom.{u, v} X n ≫ degreeInv.{u, v} X n) =
          (iσ ≫ degreeHom.{u, v} X n) ≫ degreeInv.{u, v} X n :=
        (Category.assoc _ _ _).symm
      _ = (C.hom ≫ F.map i₀) ≫ degreeInv.{u, v} X n :=
        congrArg (fun h => h ≫ degreeInv.{u, v} X n) hHom
      _ = C.hom ≫ (F.map i₀ ≫ degreeInv.{u, v} X n) := Category.assoc _ _ _
      _ = C.hom ≫ (C.inv ≫ is) := congrArg (fun h => C.hom ≫ h) hInv
      _ = is := C.hom_inv_id_assoc is
      _ = iσ := hIndex
      _ = iσ ≫ 𝟙 _ := (Category.comp_id iσ).symm
  inv_hom_id := by
    apply (isColimitOfPreserves coefficientFunctor.{u, v}
      (X.isColimitChainComplexXCofan originalCoefficients.{u} n)).hom_ext
    rintro ⟨σ⟩
    let L : SSet.{max u v} := SSet.uliftFunctor.{v, u}.obj X
    let F : AddCommGrpCat.{u} ⥤ AddCommGrpCat.{max u v} := coefficientFunctor.{u, v}
    let C := coefficientIso.{u, v}
    let s : L _⦋n⦌ := ULift.up σ
    let i₀ : originalCoefficients.{u} ⟶ (originalComplex X).X n :=
      X.ιChainComplex (R := originalCoefficients.{u}) σ
    let is : liftedCoefficients.{u, v} ⟶ (liftedComplex.{u, v} X).X n :=
      L.ιChainComplex (R := liftedCoefficients.{u, v}) s
    have hInv : F.map i₀ ≫ degreeInv.{u, v} X n = C.inv ≫ is :=
      map_ι_degreeInv.{u, v} X n σ
    have hHom : is ≫ degreeHom.{u, v} X n = C.hom ≫ F.map i₀ :=
      ι_degreeHom.{u, v} X n s
    change F.map i₀ ≫ (degreeInv.{u, v} X n ≫ degreeHom.{u, v} X n) =
      F.map i₀ ≫ 𝟙 _
    calc
      F.map i₀ ≫ (degreeInv.{u, v} X n ≫ degreeHom.{u, v} X n) =
          (F.map i₀ ≫ degreeInv.{u, v} X n) ≫ degreeHom.{u, v} X n :=
        (Category.assoc _ _ _).symm
      _ = (C.inv ≫ is) ≫ degreeHom.{u, v} X n :=
        congrArg (fun h => h ≫ degreeHom.{u, v} X n) hInv
      _ = C.inv ≫ (is ≫ degreeHom.{u, v} X n) := Category.assoc _ _ _
      _ = C.inv ≫ (C.hom ≫ F.map i₀) := congrArg (fun h => C.inv ≫ h) hHom
      _ = F.map i₀ := C.inv_hom_id_assoc (F.map i₀)
      _ = F.map i₀ ≫ 𝟙 _ := (Category.comp_id (F.map i₀)).symm

private theorem degreeHom_comm (X : SSet.{u}) (n : ℕ) :
    degreeHom.{u, v} X (n + 1) ≫
        coefficientFunctor.{u, v}.map ((originalComplex X).d (n + 1) n) =
      (liftedComplex.{u, v} X).d (n + 1) n ≫ degreeHom.{u, v} X n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_degreeHom, Category.assoc, ← Functor.map_comp,
    SSet.ιChainComplex_d, Functor.map_sum, Preadditive.comp_sum,
    SSet.ιChainComplex_d_assoc, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [Functor.map_zsmul, Preadditive.comp_zsmul, Preadditive.zsmul_comp, ι_degreeHom]
  rfl

/-- The actual integer chain comparison transports both the original
simplex indices and the original integer coefficient carrier. -/
public def chainIso (X : SSet.{u}) :
    (SSet.uliftFunctor.{v, u}.obj X).chainComplex
        AlgebraicTopology.singularIntegralCoefficients.{max u v} ≅
      (AddCommGrpCat.uliftFunctor.{v, u}.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (X.chainComplex AlgebraicTopology.singularIntegralCoefficients.{u}) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => degreeIso.{u, v} X n)
    (by
      intro i j hij
      obtain rfl : i = j + 1 := hij.symm
      exact degreeHom_comm.{u, v} X j)

@[reassoc]
public theorem chainIso_hom_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.chainComplexMap (SSet.uliftFunctor.{v, u}.map f)
        AlgebraicTopology.singularIntegralCoefficients.{max u v} ≫
      (chainIso.{u, v} Y).hom =
    (chainIso.{u, v} X).hom ≫
      (AddCommGrpCat.uliftFunctor.{v, u}.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (SSet.chainComplexMap f AlgebraicTopology.singularIntegralCoefficients.{u}) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply SSet.chainComplex_hom_ext
  intro σ
  change (SSet.uliftFunctor.{v, u}.obj X).ιChainComplex
      (R := liftedCoefficients.{u, v}) σ ≫
        ((SSet.chainComplexMap (SSet.uliftFunctor.{v, u}.map f)
          liftedCoefficients.{u, v}).f n ≫ degreeHom.{u, v} Y n) =
    (SSet.uliftFunctor.{v, u}.obj X).ιChainComplex
      (R := liftedCoefficients.{u, v}) σ ≫
        (degreeHom.{u, v} X n ≫ coefficientFunctor.{u, v}.map
          ((SSet.chainComplexMap f originalCoefficients.{u}).f n))
  rw [SSet.ι_chainComplexMap_f_assoc, ι_degreeHom,
    ← Category.assoc, ι_degreeHom, Category.assoc, ← Functor.map_comp,
    SSet.ι_chainComplexMap_f]
  rfl

private def coefficientHomologyIso (K : ChainComplex AddCommGrpCat.{u} ℕ) (n : ℕ) :
    ((coefficientFunctor.{u, v}.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).homology n ≅
      coefficientFunctor.{u, v}.obj (K.homology n) :=
  (K.sc n).mapHomologyIso coefficientFunctor.{u, v}

@[reassoc]
private theorem coefficientHomologyIso_hom_naturality
    {K L : ChainComplex AddCommGrpCat.{u} ℕ} (f : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((coefficientFunctor.{u, v}.mapHomologicalComplex (ComplexShape.down ℕ)).map f) n ≫
      (coefficientHomologyIso.{u, v} L n).hom =
    (coefficientHomologyIso.{u, v} K n).hom ≫
      coefficientFunctor.{u, v}.map (HomologicalComplex.homologyMap f n) := by
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n).map f)
    coefficientFunctor.{u, v}

/-- The induced homology Iso uses the exact additive coefficient lift. -/
public def homologyIso (X : SSet.{u}) (n : ℕ) :
    (SSet.uliftFunctor.{v, u}.obj X).homology
        AlgebraicTopology.singularIntegralCoefficients.{max u v} n ≅
      AddCommGrpCat.uliftFunctor.{v, u}.obj
        (X.homology AlgebraicTopology.singularIntegralCoefficients.{u} n) :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v}
      (ComplexShape.down ℕ) n).mapIso (chainIso.{u, v} X) ≪≫
    coefficientHomologyIso.{u, v} (originalComplex X) n

@[reassoc]
public theorem homologyIso_hom_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    SSet.homologyMap (SSet.uliftFunctor.{v, u}.map f)
        AlgebraicTopology.singularIntegralCoefficients.{max u v} n ≫
      (homologyIso.{u, v} Y n).hom =
    (homologyIso.{u, v} X n).hom ≫
      AddCommGrpCat.uliftFunctor.{v, u}.map
        (SSet.homologyMap f AlgebraicTopology.singularIntegralCoefficients.{u} n) := by
  let U := coefficientFunctor.{u, v}
  let T := U.mapHomologicalComplex (ComplexShape.down ℕ)
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v}
    (ComplexShape.down ℕ) n
  let f0 := SSet.chainComplexMap f originalCoefficients.{u}
  let fL := SSet.chainComplexMap (SSet.uliftFunctor.{v, u}.map f)
    liftedCoefficients.{u, v}
  have he (Z : SSet.{u}) : (homologyIso.{u, v} Z n).hom =
      HomologicalComplex.homologyMap (chainIso.{u, v} Z).hom n ≫
        (coefficientHomologyIso.{u, v} (originalComplex Z) n).hom := by
    have hm : (H.mapIso (chainIso.{u, v} Z)).hom =
        HomologicalComplex.homologyMap (chainIso.{u, v} Z).hom n :=
      (Functor.mapIso_hom H (chainIso.{u, v} Z)).trans
        (HomologicalComplex.homologyFunctor_map
          (C := AddCommGrpCat.{max u v}) (c := ComplexShape.down ℕ)
          (i := n) (f := (chainIso.{u, v} Z).hom))
    exact (Iso.trans_hom (H.mapIso (chainIso.{u, v} Z))
      (coefficientHomologyIso.{u, v} (originalComplex Z) n)).trans
        (congrArg (fun k : (liftedComplex.{u, v} Z).homology n ⟶
            (T.obj (originalComplex Z)).homology n =>
          k ≫ (coefficientHomologyIso.{u, v} (originalComplex Z) n).hom) hm)
  have hChain : fL ≫ (chainIso.{u, v} Y).hom =
      (chainIso.{u, v} X).hom ≫ T.map f0 := chainIso_hom_naturality.{u, v} f
  have hn :
      HomologicalComplex.homologyMap fL n ≫
          HomologicalComplex.homologyMap (chainIso.{u, v} Y).hom n =
        HomologicalComplex.homologyMap (chainIso.{u, v} X).hom n ≫
          HomologicalComplex.homologyMap (T.map f0) n := by
    calc
      _ = HomologicalComplex.homologyMap (fL ≫ (chainIso.{u, v} Y).hom) n :=
        (HomologicalComplex.homologyMap_comp
          (φ := fL) (ψ := (chainIso.{u, v} Y).hom) (i := n)).symm
      _ = HomologicalComplex.homologyMap ((chainIso.{u, v} X).hom ≫ T.map f0) n :=
        congrArg (fun k : liftedComplex.{u, v} X ⟶ T.obj (originalComplex Y) =>
          HomologicalComplex.homologyMap k n) hChain
      _ = _ := HomologicalComplex.homologyMap_comp
        (φ := (chainIso.{u, v} X).hom) (ψ := T.map f0) (i := n)
  have hp := coefficientHomologyIso_hom_naturality.{u, v} f0 n
  calc
    SSet.homologyMap (SSet.uliftFunctor.{v, u}.map f)
        AlgebraicTopology.singularIntegralCoefficients.{max u v} n ≫
          (homologyIso.{u, v} Y n).hom =
      HomologicalComplex.homologyMap fL n ≫
        (HomologicalComplex.homologyMap (chainIso.{u, v} Y).hom n ≫
          (coefficientHomologyIso.{u, v} (originalComplex Y) n).hom) :=
      congrArg (fun k : (liftedComplex.{u, v} Y).homology n ⟶
          U.obj ((originalComplex Y).homology n) =>
        HomologicalComplex.homologyMap fL n ≫ k) (he Y)
    _ = (HomologicalComplex.homologyMap fL n ≫
        HomologicalComplex.homologyMap (chainIso.{u, v} Y).hom n) ≫
          (coefficientHomologyIso.{u, v} (originalComplex Y) n).hom :=
      (Category.assoc _ _ _).symm
    _ = (HomologicalComplex.homologyMap (chainIso.{u, v} X).hom n ≫
        HomologicalComplex.homologyMap (T.map f0) n) ≫
          (coefficientHomologyIso.{u, v} (originalComplex Y) n).hom :=
      congrArg (fun k : (liftedComplex.{u, v} X).homology n ⟶
          (T.obj (originalComplex Y)).homology n =>
        k ≫ (coefficientHomologyIso.{u, v} (originalComplex Y) n).hom) hn
    _ = HomologicalComplex.homologyMap (chainIso.{u, v} X).hom n ≫
        (HomologicalComplex.homologyMap (T.map f0) n ≫
          (coefficientHomologyIso.{u, v} (originalComplex Y) n).hom) :=
      Category.assoc _ _ _
    _ = HomologicalComplex.homologyMap (chainIso.{u, v} X).hom n ≫
        ((coefficientHomologyIso.{u, v} (originalComplex X) n).hom ≫
          U.map (HomologicalComplex.homologyMap f0 n)) :=
      congrArg (fun k : (T.obj (originalComplex X)).homology n ⟶
          U.obj ((originalComplex Y).homology n) =>
        HomologicalComplex.homologyMap (chainIso.{u, v} X).hom n ≫ k) hp
    _ = (HomologicalComplex.homologyMap (chainIso.{u, v} X).hom n ≫
        (coefficientHomologyIso.{u, v} (originalComplex X) n).hom) ≫
          U.map (HomologicalComplex.homologyMap f0 n) :=
      (Category.assoc _ _ _).symm
    _ = (homologyIso.{u, v} X n).hom ≫
        U.map (HomologicalComplex.homologyMap f0 n) :=
      congrArg (fun k : (liftedComplex.{u, v} X).homology n ⟶
          U.obj ((originalComplex X).homology n) =>
        k ≫ U.map (HomologicalComplex.homologyMap f0 n)) (he X).symm

/-- The integral homology of the canonical carrier lift is the exact
abelian-group lift of the original integral homology, with both original
integer and simplex coordinates retained. -/
public def singularHomologyIso (X : TopCat.{u}) (n : ℕ) :
    (AlgebraicTopology.singularIntegralHomologyFunctor n).obj
        (TopCat.uliftFunctor.{v, u}.obj X) ≅
      AddCommGrpCat.uliftFunctor.{v, u}.obj
        ((AlgebraicTopology.singularIntegralHomologyFunctor n).obj X) :=
  by
    let lateIntegralCoproducts : HasCoproducts.{max u v} AddCommGrpCat.{max u v} :=
      originalCoproducts.{max u v}
    exact (SSet.homologyFunctor (C := AddCommGrpCat.{max u v})
      AlgebraicTopology.singularIntegralCoefficients.{max u v} n).mapIso
        (singularSSetIso.{u, v} X) ≪≫
      homologyIso.{u, v} (TopCat.toSSet.obj X) n

@[reassoc]
public theorem singularHomologyIso_hom_naturality
    {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    (AlgebraicTopology.singularIntegralHomologyFunctor n).map
        (TopCat.uliftFunctor.{v, u}.map f) ≫
      (singularHomologyIso.{u, v} Y n).hom =
    (singularHomologyIso.{u, v} X n).hom ≫
      AddCommGrpCat.uliftFunctor.{v, u}.map
        ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f) := by
  let lateIntegralCoproducts : HasCoproducts.{max u v} AddCommGrpCat.{max u v} :=
    originalCoproducts.{max u v}
  let U := AddCommGrpCat.uliftFunctor.{v, u}
  let L := SSet.uliftFunctor.{v, u}
  let cL := AlgebraicTopology.singularIntegralCoefficients.{max u v}
  let cO := AlgebraicTopology.singularIntegralCoefficients.{u}
  let H := SSet.homologyFunctor (C := AddCommGrpCat.{max u v}) cL n
  let f0 := TopCat.toSSet.map f
  let fL := TopCat.toSSet.map (TopCat.uliftFunctor.{v, u}.map f)
  have hOriginalView : AlgebraicTopology.singularIntegralHomologyFunctor.{u} n =
      TopCat.toSSet.{u} ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u}) cO n := rfl
  have hLiftedView : AlgebraicTopology.singularIntegralHomologyFunctor.{max u v} n =
      TopCat.toSSet.{max u v} ⋙ H := rfl
  have he (Z : TopCat.{u}) : (singularHomologyIso.{u, v} Z n).hom =
      SSet.homologyMap (C := AddCommGrpCat.{max u v})
          (singularSSetIso.{u, v} Z).hom cL n ≫
        (homologyIso.{u, v} (TopCat.toSSet.obj Z) n).hom := by
    have hm : (H.mapIso (singularSSetIso.{u, v} Z)).hom =
        SSet.homologyMap (C := AddCommGrpCat.{max u v})
          (singularSSetIso.{u, v} Z).hom cL n :=
      (Functor.mapIso_hom H (singularSSetIso.{u, v} Z)).trans
        (SSet.homologyFunctor_map (C := AddCommGrpCat.{max u v})
          cL n (singularSSetIso.{u, v} Z).hom)
    exact (Iso.trans_hom (H.mapIso (singularSSetIso.{u, v} Z))
      (homologyIso.{u, v} (TopCat.toSSet.obj Z) n)).trans
        (congrArg (fun k :
            (TopCat.toSSet.obj (TopCat.uliftFunctor.{v, u}.obj Z)).homology cL n ⟶
              (L.obj (TopCat.toSSet.obj Z)).homology cL n =>
          k ≫ (homologyIso.{u, v} (TopCat.toSSet.obj Z) n).hom) hm)
  have hSing : fL ≫ (singularSSetIso.{u, v} Y).hom =
      (singularSSetIso.{u, v} X).hom ≫ L.map f0 :=
    singularSSetIso_hom_naturality.{u, v} f
  have hn : SSet.homologyMap (C := AddCommGrpCat.{max u v}) fL cL n ≫
        SSet.homologyMap (C := AddCommGrpCat.{max u v})
          (singularSSetIso.{u, v} Y).hom cL n =
      SSet.homologyMap (C := AddCommGrpCat.{max u v})
          (singularSSetIso.{u, v} X).hom cL n ≫
        SSet.homologyMap (C := AddCommGrpCat.{max u v}) (L.map f0) cL n := by
    calc
      _ = SSet.homologyMap (C := AddCommGrpCat.{max u v})
          (fL ≫ (singularSSetIso.{u, v} Y).hom) cL n :=
        (SSet.homologyMap_comp (C := AddCommGrpCat.{max u v})
          (f := fL) (g := (singularSSetIso.{u, v} Y).hom) (R := cL) (n := n)).symm
      _ = SSet.homologyMap (C := AddCommGrpCat.{max u v})
          ((singularSSetIso.{u, v} X).hom ≫ L.map f0) cL n :=
        congrArg (fun k : TopCat.toSSet.obj (TopCat.uliftFunctor.{v, u}.obj X) ⟶
            L.obj (TopCat.toSSet.obj Y) =>
          SSet.homologyMap (C := AddCommGrpCat.{max u v}) k cL n) hSing
      _ = _ := SSet.homologyMap_comp (C := AddCommGrpCat.{max u v})
        (f := (singularSSetIso.{u, v} X).hom) (g := L.map f0) (R := cL) (n := n)
  have hp := homologyIso_hom_naturality.{u, v} f0 n
  change SSet.homologyMap (C := AddCommGrpCat.{max u v}) (L.map f0) cL n ≫
      (homologyIso.{u, v} (TopCat.toSSet.obj Y) n).hom =
    (homologyIso.{u, v} (TopCat.toSSet.obj X) n).hom ≫
      U.map (SSet.homologyMap (C := AddCommGrpCat.{u}) f0 cO n) at hp
  have hY :
      (SSet.homologyMap (C := AddCommGrpCat.{max u v}) fL cL n ≫
        (singularHomologyIso.{u, v} Y n).hom :
          (TopCat.toSSet.obj (TopCat.uliftFunctor.{v, u}.obj X)).homology cL n ⟶
            U.obj ((TopCat.toSSet.obj Y).homology cO n)) =
      SSet.homologyMap (C := AddCommGrpCat.{max u v}) fL cL n ≫
        (SSet.homologyMap (C := AddCommGrpCat.{max u v})
          (singularSSetIso.{u, v} Y).hom cL n ≫
            (homologyIso.{u, v} (TopCat.toSSet.obj Y) n).hom) :=
    congrArg (fun k :
        (TopCat.toSSet.obj (TopCat.uliftFunctor.{v, u}.obj Y)).homology cL n ⟶
          U.obj ((TopCat.toSSet.obj Y).homology cO n) =>
      SSet.homologyMap (C := AddCommGrpCat.{max u v}) fL cL n ≫ k) (he Y)
  have hCanonical :
      SSet.homologyMap (C := AddCommGrpCat.{max u v}) fL cL n ≫
        (SSet.homologyMap (C := AddCommGrpCat.{max u v})
          (singularSSetIso.{u, v} Y).hom cL n ≫
            (homologyIso.{u, v} (TopCat.toSSet.obj Y) n).hom) =
      (SSet.homologyMap (C := AddCommGrpCat.{max u v})
          (singularSSetIso.{u, v} X).hom cL n ≫
        (homologyIso.{u, v} (TopCat.toSSet.obj X) n).hom) ≫
          U.map (SSet.homologyMap (C := AddCommGrpCat.{u}) f0 cO n) := by
    rw [← Category.assoc, hn, Category.assoc, hp, ← Category.assoc]
  have hX :
      (SSet.homologyMap (C := AddCommGrpCat.{max u v})
          (singularSSetIso.{u, v} X).hom cL n ≫
        (homologyIso.{u, v} (TopCat.toSSet.obj X) n).hom) ≫
          U.map (SSet.homologyMap (C := AddCommGrpCat.{u}) f0 cO n) =
      ((singularHomologyIso.{u, v} X n).hom ≫
        U.map (SSet.homologyMap (C := AddCommGrpCat.{u}) f0 cO n) :
          (TopCat.toSSet.obj (TopCat.uliftFunctor.{v, u}.obj X)).homology cL n ⟶
            U.obj ((TopCat.toSSet.obj Y).homology cO n)) :=
    congrArg (fun k :
        (TopCat.toSSet.obj (TopCat.uliftFunctor.{v, u}.obj X)).homology cL n ⟶
          U.obj ((TopCat.toSSet.obj X).homology cO n) =>
      k ≫ U.map (SSet.homologyMap (C := AddCommGrpCat.{u}) f0 cO n)) (he X).symm
  have hOrigObj (Z : TopCat.{u}) :
      (AlgebraicTopology.singularIntegralHomologyFunctor.{u} n).obj Z =
        (TopCat.toSSet.obj Z).homology cO n :=
    (Functor.congr_obj hOriginalView Z).trans
      (SSet.homologyFunctor_obj (C := AddCommGrpCat.{u}) cO n (TopCat.toSSet.obj Z))
  have hLiftObj (Z : TopCat.{max u v}) :
      (AlgebraicTopology.singularIntegralHomologyFunctor.{max u v} n).obj Z =
        (TopCat.toSSet.obj Z).homology cL n :=
    (Functor.congr_obj hLiftedView Z).trans
      (SSet.homologyFunctor_obj (C := AddCommGrpCat.{max u v})
        cL n (TopCat.toSSet.obj Z))
  have hMapLift :
      (AlgebraicTopology.singularIntegralHomologyFunctor.{max u v} n).map
          (TopCat.uliftFunctor.{v, u}.map f) ≍
        SSet.homologyMap (C := AddCommGrpCat.{max u v}) fL cL n :=
    (Functor.hcongr_hom hLiftedView (TopCat.uliftFunctor.{v, u}.map f)).trans
      (heq_of_eq (SSet.homologyFunctor_map (C := AddCommGrpCat.{max u v}) cL n fL))
  have hMapOrig :
      U.map ((AlgebraicTopology.singularIntegralHomologyFunctor.{u} n).map f) ≍
        U.map (SSet.homologyMap (C := AddCommGrpCat.{u}) f0 cO n) :=
    (Functor.postcomp_map_heq U
      (Functor.congr_obj hOriginalView X) (Functor.congr_obj hOriginalView Y)
      (Functor.hcongr_hom hOriginalView f)).trans
        (heq_of_eq (congrArg (fun k => U.map k)
          (SSet.homologyFunctor_map (C := AddCommGrpCat.{u}) cO n f0)))
  have hLeft :
      ((AlgebraicTopology.singularIntegralHomologyFunctor.{max u v} n).map
        (TopCat.uliftFunctor.{v, u}.map f) ≫ (singularHomologyIso.{u, v} Y n).hom) ≍
      (SSet.homologyMap (C := AddCommGrpCat.{max u v}) fL cL n ≫
        (singularHomologyIso.{u, v} Y n).hom :
          (TopCat.toSSet.obj (TopCat.uliftFunctor.{v, u}.obj X)).homology cL n ⟶
            U.obj ((TopCat.toSSet.obj Y).homology cO n)) :=
    CategoryTheory.heq_comp (hLiftObj (TopCat.uliftFunctor.{v, u}.obj X))
      (hLiftObj (TopCat.uliftFunctor.{v, u}.obj Y))
      (congrArg U.obj (hOrigObj Y)) hMapLift HEq.rfl
  have hRight :
      ((singularHomologyIso.{u, v} X n).hom ≫
        U.map ((AlgebraicTopology.singularIntegralHomologyFunctor.{u} n).map f)) ≍
      ((singularHomologyIso.{u, v} X n).hom ≫
        U.map (SSet.homologyMap (C := AddCommGrpCat.{u}) f0 cO n) :
          (TopCat.toSSet.obj (TopCat.uliftFunctor.{v, u}.obj X)).homology cL n ⟶
            U.obj ((TopCat.toSSet.obj Y).homology cO n)) :=
    CategoryTheory.heq_comp (hLiftObj (TopCat.uliftFunctor.{v, u}.obj X))
      (congrArg U.obj (hOrigObj X)) (congrArg U.obj (hOrigObj Y)) HEq.rfl hMapOrig
  exact eq_of_heq
    (hLeft.trans ((heq_of_eq (hY.trans (hCanonical.trans hX))).trans hRight.symm))

/-- Isomorphy of the original integral homology map implies isomorphy of
its actual carrier lift. The comparison premise is the original map. -/
public theorem singularIntegralHomology_uliftMap_isIso
    {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ)
    [IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor.{u} n).map f)] :
    IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor.{max u v} n).map
      (TopCat.uliftFunctor.{v, u}.map f)) := by
  let lateIntegralCoproducts : HasCoproducts.{max u v} AddCommGrpCat.{max u v} :=
    originalCoproducts.{max u v}
  have h : (AlgebraicTopology.singularIntegralHomologyFunctor.{max u v} n).map
        (TopCat.uliftFunctor.{v, u}.map f) ≫ (singularHomologyIso.{u, v} Y n).hom =
      (singularHomologyIso.{u, v} X n).hom ≫ AddCommGrpCat.uliftFunctor.{v, u}.map
        ((AlgebraicTopology.singularIntegralHomologyFunctor.{u} n).map f) :=
    singularHomologyIso_hom_naturality.{u, v} f n
  exact IsIso.of_isIso_fac_right h

/-- The actual integral acyclicity predicate transports to the canonical
carrier lift. Nonemptiness is used only to obtain the old terminal-map
criterion; the plus application supplies its original explicit fiber point. -/
public theorem isAcyclicSpace_ulift (X : TopCat.{u}) [Nonempty X]
    (hX : TopCat.IsAcyclicSpace X) :
    TopCat.IsAcyclicSpace (TopCat.uliftFunctor.{v, u}.obj X) := by
  let U := TopCat.uliftFunctor.{v, u}
  let liftedCarrierNonempty : Nonempty (U.obj X) :=
    Nonempty.map (TopCat.uliftFunctorObjHomeo.{v, u} X)
      (inferInstance : Nonempty X)
  apply (TopCat.isAcyclicSpace_iff_terminalHomology_isIso (U.obj X)).2
  intro n
  let lateIntegralCoproducts : HasCoproducts.{max u v} AddCommGrpCat.{max u v} :=
    originalCoproducts.{max u v}
  let H := AlgebraicTopology.singularIntegralHomologyFunctor.{max u v} n
  let : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor.{u} n).map
      (terminal.from X)) :=
    ((TopCat.isAcyclicSpace_iff_terminalHomology_isIso X).1 hX) n
  let : IsIso (H.map (U.map (terminal.from X))) :=
    singularIntegralHomology_uliftMap_isIso.{u, v} (terminal.from X) n
  have ht : terminal.from (U.obj X) =
      U.map (terminal.from X) ≫ terminalComparison U :=
    terminalIsTerminal.hom_ext _ _
  rw [ht, H.map_comp]
  infer_instance

end AlgebraicTopology.IntegralUniverseLift
