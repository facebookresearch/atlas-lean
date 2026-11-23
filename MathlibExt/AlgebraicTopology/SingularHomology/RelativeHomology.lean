/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

import MathlibExt.Algebra.Homology.HomologySequenceFunctor

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import MathlibExt.Topology.Category.TopPair
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import MathlibExt.Algebra.Homology.ShortComplex.CokernelSequence

/-!
# Relative singular homology

The primary mathematically faithful API is `relativeSingularHomologyFunctor` on `TopPair`,
defined functorially as:

`TopPair → Arrow TopCat → Arrow (ChainComplex C) → coker → homology`.

The functorial short exact sequence is obtained via `ShortComplex.functorEquivalence`
and the connecting morphism via `HomologySequence.δ_naturality`.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial SimplexCategory

namespace AlgebraicTopology

universe w v u

section RelativeFunctor

variable (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- The underlying arrow of a topological pair. -/
abbrev topPairArrowFunctor : TopPair.{w} ⥤ Arrow TopCat.{w} :=
  MorphismProperty.Arrow.forget _ _ _

/-- Apply fixed-coefficient singular chains to the inclusion in a topological pair. -/
noncomputable def singularPairChainArrowFunctor (R : C) :
    TopPair.{w} ⥤ Arrow (ChainComplex C ℕ) :=
  topPairArrowFunctor ⋙ ((singularChainComplexFunctor C).obj R).mapArrow

/-- The singular-chain arrow of a pair lands in monomorphisms, presented as a functor into
the arrow subcategory of monomorphisms. -/
noncomputable def singularPairChainMonoArrowFunctor (R : C) :
    TopPair.{w} ⥤ (MorphismProperty.monomorphisms (ChainComplex C ℕ)).Arrow ⊤ ⊤ :=
  MorphismProperty.Comma.lift
    (F := (singularPairChainArrowFunctor C R :
      TopPair.{w} ⥤ Comma (𝟭 (ChainComplex C ℕ)) (𝟭 (ChainComplex C ℕ))))
    (fun P => by
      have : Mono P.map := inferInstance
      change Mono (((singularChainComplexFunctor C).obj R).map P.map)
      infer_instance)
    (fun _ => trivial)
    (fun _ => trivial)

/-- The functor `TopPair ⥤ ShortComplex (ChainComplex C ℕ)` sending a pair to
`C(A) ⟶ C(X) ⟶ C(X,A)` via the monomorphism arrow of singular chains and the
functorial cokernel sequence. -/
noncomputable def singularPairCokernelSequenceFunctor (R : C) :
    TopPair.{w} ⥤ ShortComplex (ChainComplex C ℕ) :=
  singularPairChainMonoArrowFunctor C R ⋙
    MorphismProperty.Arrow.forget _ _ _ ⋙
    CategoryTheory.ShortComplex.cokernelSequenceFunctor

/-- The relative singular chain complex, functorially defined as a cokernel. -/
noncomputable def relativeSingularChainFunctor (R : C) :
    TopPair.{w} ⥤ ChainComplex C ℕ :=
  singularPairCokernelSequenceFunctor C R ⋙ ShortComplex.π₃

noncomputable def relativeSingularChainQuotient (R : C) (P : TopPair.{w}) :
    ((singularChainComplexFunctor C).obj R).obj P.fst ⟶ (relativeSingularChainFunctor C R).obj P :=
  ((singularPairCokernelSequenceFunctor C R).obj P).g

@[reassoc]
theorem relativeSingularChainQuotient_naturality (R : C) {P Q : TopPair.{w}} (f : P ⟶ Q) :
    relativeSingularChainQuotient C R P ≫ (relativeSingularChainFunctor C R).map f =
      ((singularChainComplexFunctor C).obj R).map (TopPair.Hom.fst f) ≫
        relativeSingularChainQuotient C R Q :=
  ((singularPairCokernelSequenceFunctor C R).map f).comm₂₃.symm

/-- The quotient from absolute to relative singular chains, natural in topological pairs. -/
noncomputable def relativeSingularChainQuotientNatTrans (R : C) :
    TopPair.proj₁ ⋙ (singularChainComplexFunctor C).obj R ⟶
      relativeSingularChainFunctor C R where
  app P := relativeSingularChainQuotient C R P
  naturality _ _ f := (relativeSingularChainQuotient_naturality C R f).symm

/-- Relative singular homology of topological pairs. -/
noncomputable def relativeSingularHomologyFunctor (R : C) (n : ℕ) : TopPair.{w} ⥤ C :=
  relativeSingularChainFunctor C R ⋙
    HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n

/-- Objectwise form of the singular-pair short complex. -/
noncomputable def singularPairShortComplexFunctor (R : C) :
    TopPair.{w} ⥤ ShortComplex (ChainComplex C ℕ) :=
  singularPairCokernelSequenceFunctor C R

lemma singularPairShortComplex_shortExact (R : C) (P : TopPair.{w}) :
    ((singularPairShortComplexFunctor C R).obj P).ShortExact := by
  have : Mono
      ((MorphismProperty.Arrow.forget (MorphismProperty.monomorphisms (ChainComplex C ℕ)) ⊤ ⊤).obj
        ((singularPairChainMonoArrowFunctor C R).obj P)).hom := by
    change Mono ((singularPairChainMonoArrowFunctor C R).obj P).hom
    exact (singularPairChainMonoArrowFunctor C R).obj P |>.prop
  exact CategoryTheory.ShortComplex.cokernelSequence_shortExact _

/-- The connecting morphism `H_{n+1}(X,A;R) ⟶ H_n(A;R)`, natural in the pair. -/
noncomputable def relativeSingularBoundary (R : C) (n : ℕ) :
    relativeSingularHomologyFunctor C R (n + 1) ⟶
      TopPair.proj₂ ⋙ (singularHomologyFunctor C n).obj R :=
  HomologicalComplex.HomologySequence.δNatTransOfFamily
    (singularPairShortComplexFunctor C R)
    (singularPairShortComplex_shortExact C R) (n + 1) n (by simp)

lemma isZero_sigmaConst_of_isEmpty (R : C) (T : Type w) [IsEmpty T] :
    IsZero ((sigmaConst.obj R).obj T) := by
  have hT : IsInitial T := ((Types.initial_iff_empty T).2 inferInstance).some
  have hI : IsInitial ((sigmaConst.obj R).obj T) :=
    IsInitial.isInitialObj (sigmaConst.obj R) T hT
  exact (isZero_zero C).of_iso (HasZeroObject.zeroIsoIsInitial hI).symm

lemma isZero_singularChainFunctor_of_isEmpty (R : C) (Z : TopCat.{w}) [IsEmpty Z] :
    IsZero (((singularChainComplexFunctor C).obj R).obj Z) := by
  rw [IsZero.iff_id_eq_zero]
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  have : IsEmpty C(Convexity.StdSimplex ℝ (Fin ((Opposite.op ⦋n⦌).unop.len + 1)), Z) :=
    ⟨fun f => isEmptyElim (f (Classical.arbitrary _))⟩
  have : IsEmpty ((TopCat.toSSet.obj Z).obj (Opposite.op ⦋n⦌)) :=
    Function.isEmpty (TopCat.toSSetObjEquiv Z (Opposite.op ⦋n⦌))
  exact (isZero_sigmaConst_of_isEmpty C R
    ((TopCat.toSSet.obj Z).obj (Opposite.op ⦋n⦌))).eq_of_src _ _

noncomputable instance isIso_singularPairShortComplex_g_of_isEmpty
    (R : C) (P : TopPair.{w}) [IsEmpty P.snd] :
    IsIso ((singularPairShortComplexFunctor C R).obj P).g :=
  (singularPairShortComplex_shortExact C R P).isIso_g_iff.mpr
    (isZero_singularChainFunctor_of_isEmpty C R P.snd)

/-- Relative homology of `(X, ∅)` naturally agrees with absolute homology. -/
noncomputable def singularHomologyEmptyPairIso (R : C) (n : ℕ) :
    (singularHomologyFunctor C n).obj R ≅
      TopPair.incl ⋙ relativeSingularHomologyFunctor C R n :=
  NatIso.ofComponents
    (fun X => by
      haveI : IsEmpty (TopPair.incl.obj X).snd := inferInstanceAs (IsEmpty PEmpty)
      exact HomologicalComplex.homologyMapIso
        (asIso ((singularPairShortComplexFunctor C R).obj (TopPair.incl.obj X)).g) n)
    (fun {X Y} f => by
      change ((singularHomologyFunctor C n).obj R).map f ≫
          HomologicalComplex.homologyMap
            ((singularPairShortComplexFunctor C R).obj (TopPair.incl.obj Y)).g n =
        HomologicalComplex.homologyMap
            ((singularPairShortComplexFunctor C R).obj (TopPair.incl.obj X)).g n ≫
          (relativeSingularHomologyFunctor C R n).map (TopPair.incl.map f)
      exact ((HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n).mapShortComplex.map
        ((singularPairShortComplexFunctor C R).map (TopPair.incl.map f))).comm₂₃)

/-- The canonical map from absolute homology of the ambient space to relative
homology of a pair, induced by the quotient of singular chains. -/
noncomputable def singularHomologyPairQuotientMap (R : C) (P : TopPair.{w})
    (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).obj P.fst ⟶
      (relativeSingularHomologyFunctor C R n).obj P :=
  HomologicalComplex.homologyMap (relativeSingularChainQuotient C R P) n

/-- The canonical map agrees with the empty-pair isomorphism followed by
the `TopPair.j` inclusion. -/
theorem singularHomologyPairQuotientMap_eq_app_comp_j (R : C) (P : TopPair.{w})
    (n : ℕ) :
    singularHomologyPairQuotientMap C R P n =
      (singularHomologyEmptyPairIso C R n).hom.app P.fst ≫
        (relativeSingularHomologyFunctor C R n).map (TopPair.j P) := by
  have happ : (singularHomologyEmptyPairIso C R n).hom.app P.fst =
      HomologicalComplex.homologyMap
        (relativeSingularChainQuotient C R (TopPair.incl.obj P.fst)) n := rfl
  have hrel : (relativeSingularHomologyFunctor C R n).map (TopPair.j P) =
      HomologicalComplex.homologyMap
        ((relativeSingularChainFunctor C R).map (TopPair.j P)) n := rfl
  have hnat : relativeSingularChainQuotient C R (TopPair.incl.obj P.fst) ≫
        (relativeSingularChainFunctor C R).map (TopPair.j P) =
      relativeSingularChainQuotient C R P := by
    have hmid : ((singularChainComplexFunctor C).obj R).map
          (TopPair.Hom.fst (TopPair.j P)) =
        𝟙 (((singularChainComplexFunctor C).obj R).obj P.fst) := by
      rw [show TopPair.Hom.fst (TopPair.j P) = 𝟙 P.fst from rfl]
      exact CategoryTheory.Functor.map_id _ _
    rw [relativeSingularChainQuotient_naturality, hmid]
    exact Category.id_comp _
  rw [happ, hrel]
  change HomologicalComplex.homologyMap (relativeSingularChainQuotient C R P)
      n = _
  exact ((HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    (congrArg (fun φ => HomologicalComplex.homologyMap φ n) hnat)).symm

/-- The canonical map kills classes coming from the subspace. -/
theorem singularHomologyMap_snd_comp_singularHomologyPairQuotientMap
    (R : C) (P : TopPair.{w}) (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).map P.map ≫
      singularHomologyPairQuotientMap C R P n = 0 := by
  have hz : ((singularChainComplexFunctor C).obj R).map P.map ≫
      relativeSingularChainQuotient C R P = 0 :=
    ((singularPairShortComplexFunctor C R).obj P).zero
  have hsing : ((singularHomologyFunctor C n).obj R).map P.map =
      HomologicalComplex.homologyMap
        (((singularChainComplexFunctor C).obj R).map P.map) n := rfl
  rw [hsing]
  change HomologicalComplex.homologyMap
      (((singularChainComplexFunctor C).obj R).map P.map) n ≫
      HomologicalComplex.homologyMap (relativeSingularChainQuotient C R P)
        n = 0
  exact (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (fun φ => HomologicalComplex.homologyMap φ n) hz).trans
      (HomologicalComplex.homologyMap_zero _ _ _))

/-- The canonical map is natural under maps of pairs: pushing a class
forward along a pair map commutes with passing to relative homology. -/
theorem singularHomologyPairQuotientMap_naturality (R : C) (n : ℕ)
    {P Q : TopPair.{w}} (F : P ⟶ Q) :
    singularHomologyPairQuotientMap C R P n ≫
        (relativeSingularHomologyFunctor C R n).map F =
      ((singularHomologyFunctor C n).obj R).map (TopPair.Hom.fst F) ≫
        singularHomologyPairQuotientMap C R Q n := by
  have hrel : (relativeSingularHomologyFunctor C R n).map F =
      HomologicalComplex.homologyMap
        ((relativeSingularChainFunctor C R).map F) n := rfl
  have hsing : ((singularHomologyFunctor C n).obj R).map (TopPair.Hom.fst F) =
      HomologicalComplex.homologyMap
        (((singularChainComplexFunctor C).obj R).map (TopPair.Hom.fst F)) n := rfl
  rw [hrel, hsing]
  change HomologicalComplex.homologyMap (relativeSingularChainQuotient C R P)
        n ≫
      HomologicalComplex.homologyMap ((relativeSingularChainFunctor C R).map F)
        n =
    HomologicalComplex.homologyMap
        (((singularChainComplexFunctor C).obj R).map (TopPair.Hom.fst F)) n ≫
      HomologicalComplex.homologyMap (relativeSingularChainQuotient C R Q) n
  exact (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (fun φ => HomologicalComplex.homologyMap φ n)
      (relativeSingularChainQuotient_naturality C R F)).trans
      (HomologicalComplex.homologyMap_comp _ _ n))

end RelativeFunctor

end AlgebraicTopology
