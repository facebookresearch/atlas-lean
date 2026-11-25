/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.CotangentKaehlerAugmentation
public import MathlibExt.Algebra.Category.CommAlgCat.CotangentHomology
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# The genuine polynomial cotangent comparison with ordinary differentials

The actual polynomial row contraction is composed with the native terminal
unitor. Its forward chain map is the actual cotangent augmentation to Ω(A/k).
Tensoring this homotopy equivalence with arbitrary coefficients gives the
polynomial vanishing statement without coefficient flatness or projectivity.

The presentation input is an ordinary polynomial algebra presentation; no
cotangent or homology comparison is supplied. Candidate source; UNEXECUTED.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped TensorProduct

universe u v t

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/-- The actual point change from terminal linearization to ordinary differentials. -/
def cotangentKaehlerAugmentedIso :
    polynomialCotangentAugmented k A (Over.mk (𝟙 A)) ≅ cotangentKaehlerAugmented k A :=
  Comma.isoMk (Iso.refl _) (cotangentTerminalIso k A) (by
    change 𝟙 _ ≫ cotangentKaehlerAugmentation k A = _
    rw [Category.id_comp]
    rfl)

/-- Native augmentation naturality identifies the actual chain map after point change. -/
theorem cotangentKaehlerNormalizedAugmentation_factorization :
    cotangentKaehlerNormalizedAugmentation k A =
      polynomialCotangentNormalizedAugmentation k A (Over.mk (𝟙 A)) ≫
        (ChainComplex.single₀ (ModuleCat.{max u v} A)).map (cotangentTerminalIso k A).hom := by
  have h := AlternatingFaceMapComplex.ε.naturality (cotangentKaehlerAugmentedIso k A).hom
  change (alternatingFaceMapComplex (ModuleCat.{max u v} A)).map (𝟙 _) ≫
      AlternatingFaceMapComplex.ε.app (cotangentKaehlerAugmented k A) =
    AlternatingFaceMapComplex.ε.app
      (polynomialCotangentAugmented k A (Over.mk (𝟙 A))) ≫
        (ChainComplex.single₀ (ModuleCat.{max u v} A)).map (cotangentTerminalIso k A).hom at h
  have hid := (alternatingFaceMapComplex (ModuleCat.{max u v} A)).map_id
    (SimplicialObject.Augmented.drop.obj (cotangentKaehlerAugmented k A))
  have h' := (congrArg (fun f => f ≫ AlternatingFaceMapComplex.ε.app
    (cotangentKaehlerAugmented k A)) hid.symm).trans h
  have h'' := (Category.id_comp _).symm.trans h'
  clear h h'
  have h := h''

  unfold cotangentKaehlerNormalizedAugmentation polynomialCotangentNormalizedAugmentation
  exact (congrArg (fun f => inclusionOfMooreComplexMap
    ((polynomialCotangentSimplicialFunctor k A).obj (Over.mk (𝟙 A))) ≫ f) h).trans
      (Category.assoc _ _ _).symm

/-- The actual canonical polynomial cotangent model is homotopy equivalent to Ω(A/k)[0]. -/
def polynomialCotangentHomotopyEquivKaehler (σ : Type (max u v))
    (e : (free.{u, v} k).obj σ ≅ A) :
    HomotopyEquiv (cotangentComplex k A)
      ((ChainComplex.single₀ (ModuleCat.{max u v} A)).obj
        (ModuleCat.of A (KaehlerDifferential k A))) :=
  (polynomialCotangentAugmentationHomotopyEquiv k A (Over.mk (𝟙 A)) σ e).trans
    (HomotopyEquiv.ofIso ((ChainComplex.single₀ (ModuleCat.{max u v} A)).mapIso
      (cotangentTerminalIso k A)))

theorem polynomialCotangentKaehlerAugmentation_quasiIso (σ : Type (max u v))
    (e : (free.{u, v} k).obj σ ≅ A) :
    QuasiIso (cotangentKaehlerNormalizedAugmentation k A) := by
  letI : QuasiIso (polynomialCotangentNormalizedAugmentation k A (Over.mk (𝟙 A))) :=
    polynomialCotangentNormalizedAugmentation_quasiIso k A (Over.mk (𝟙 A)) σ e
  letI : IsIso ((ChainComplex.single₀ (ModuleCat.{max u v} A)).map
      (cotangentTerminalIso k A).hom) :=
    ((ChainComplex.single₀ (ModuleCat.{max u v} A)).mapIso (cotangentTerminalIso k A)).isIso_hom
  have h := (polynomialCotangentHomotopyEquivKaehler k A σ e).quasiIso_hom
  change QuasiIso (polynomialCotangentNormalizedAugmentation k A (Over.mk (𝟙 A)) ≫
    (ChainComplex.single₀ (ModuleCat.{max u v} A)).map (cotangentTerminalIso k A).hom) at h
  exact (cotangentKaehlerNormalizedAugmentation_factorization k A).symm ▸ h

/-- The same actual polynomial homotopy equivalence with arbitrary coefficients. -/
def polynomialCotangentCoefficientHomotopyEquiv (σ : Type (max u v))
    (e : (free.{u, v} k).obj σ ≅ A) (M : ModuleCat.{t} A) :
    HomotopyEquiv ((cotangentCoefficientComplexFunctor k A).obj M)
      ((ChainComplex.single₀ (ModuleCat.{max u v t} A)).obj
        (ModuleCat.of A (M ⊗[A] KaehlerDifferential k A))) := by
  let F := (ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M
  exact (F.mapHomotopyEquiv (polynomialCotangentHomotopyEquivKaehler k A σ e)).trans
    (HomotopyEquiv.ofIso ((HomologicalComplex.singleMapHomologicalComplex F
      (ComplexShape.down ℕ) 0).app (ModuleCat.of A (KaehlerDifferential k A))))

/-- Positive polynomial AQ homology vanishes for arbitrary coefficients by the
actual homotopy equivalence, including coefficients with torsion. -/
theorem andreQuillenHomology_isZero_of_polynomial (σ : Type (max u v))
    (e : (free.{u, v} k).obj σ ≅ A) (M : ModuleCat.{t} A) (n : ℕ) :
    IsZero (andreQuillenHomology k A M (n + 1)) := by
  let E := polynomialCotangentCoefficientHomotopyEquiv k A σ e M
  letI : QuasiIso E.hom := E.quasiIso_hom
  have hzero : IsZero (((ChainComplex.single₀ (ModuleCat.{max u v t} A)).obj
      (ModuleCat.of A (M ⊗[A] KaehlerDifferential k A))).homology (n + 1)) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact ChainComplex.exactAt_succ_single_obj _ n
  letI : QuasiIsoAt E.hom (n + 1) := inferInstance
  let eH := asIso (HomologicalComplex.homologyMap E.hom (n + 1))
  exact hzero.of_iso eH

end CommAlgCat

end
