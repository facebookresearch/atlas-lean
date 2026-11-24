/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.SplitExact
public import MathlibExt.Algebra.Homology.HomologicalComplex.SplittingFunctorTransport

/-!
# Exact-functor transport of split complexes

The forward split-exact map uses only zero morphisms and preservation of the
left/right homology data of the actual short complex at each degree. Native
exactness already supplies its homology data. Whole-category homology, abelian
structure and even additivity are unnecessary for this raw transport.

The normalized contracting-component law additionally uses an additive base
functor between preadditive categories. A native homology-preserving functor
or finite-limit/finite-colimit-preserving functor supplies the local instances.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HomologicalComplex

universe u v w uD vD

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D]
  {ι : Type w} {c : ComplexShape ι} {K : HomologicalComplex C c}

/-- Native local homology preservation earns homology of the mapped complex at one degree. -/
lemma hasHomology_map_of_preservesHomologyOf (K : HomologicalComplex C c)
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (i : ι) [K.HasHomology i]
    [F.PreservesLeftHomologyOf (K.sc i)] [F.PreservesRightHomologyOf (K.sc i)] :
    ((F.mapHomologicalComplex c).obj K).HasHomology i := by
  change ((K.sc i).map F).HasHomology
  infer_instance

/-- Preserve native acyclicity using the actual short-complex preservation instances. -/
lemma acyclic_map_of_preservesHomologyOf (hK : K.Acyclic) (F : C ⥤ D)
    [F.PreservesZeroMorphisms]
    [∀ i, F.PreservesLeftHomologyOf (K.sc i)]
    [∀ i, F.PreservesRightHomologyOf (K.sc i)] :
    ((F.mapHomologicalComplex c).obj K).Acyclic := by
  intro i
  change ((K.sc i).map F).Exact
  exact (hK i).map F

/-- Split exactness is preserved under the actual native local homology hypotheses. -/
lemma IsSplitExact.map (hK : IsSplitExact K) (F : C ⥤ D)
    [F.PreservesZeroMorphisms]
    [∀ i, F.PreservesLeftHomologyOf (K.sc i)]
    [∀ i, F.PreservesRightHomologyOf (K.sc i)] :
    IsSplitExact ((F.mapHomologicalComplex c).obj K) :=
  ⟨hK.1.map F, acyclic_map_of_preservesHomologyOf hK.2 F⟩

end HomologicalComplex

namespace Homotopy

universe u v w uD vD uE vE

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {D : Type uD} [Category.{vD} D] [Preadditive D]
  {ι : Type w} {c : ComplexShape ι} {K : HomologicalComplex C c}

/-- Retarget the native mapped contraction to the actual mapped identity and zero morphisms. -/
noncomputable def mapIdZero (h : Homotopy (𝟙 K) 0) (F : C ⥤ D) [F.Additive] :
    Homotopy (𝟙 ((F.mapHomologicalComplex c).obj K)) 0 where
  hom := (F.mapHomotopy h).hom
  zero := (F.mapHomotopy h).zero
  comm i := by
    have hId := HomologicalComplex.congr_hom ((F.mapHomologicalComplex c).map_id K) i
    exact hId.symm.trans (by
      simpa only [Functor.map_zero] using (F.mapHomotopy h).comm i)

/-- The endpoint bridge keeps precisely the native functor image of every contraction component. -/
@[simp]
lemma mapIdZero_hom (h : Homotopy (𝟙 K) 0) (F : C ⥤ D) [F.Additive] (i j : ι) :
    (h.mapIdZero F).hom i j = F.map (h.hom i j) := rfl

/-- The actual contraction components are unchanged by the identity functor. -/
lemma mapIdZero_id_hom (h : Homotopy (𝟙 K) 0) (i j : ι) :
    (h.mapIdZero (𝟭 C)).hom i j = h.hom i j := rfl

/-- Successive additive functors and their composite have the same native contraction components. -/
lemma mapIdZero_comp_hom {E : Type uE} [Category.{vE} E] [Preadditive E]
    (h : Homotopy (𝟙 K) 0) (F : C ⥤ D) [F.Additive]
    (G : D ⥤ E) [G.Additive] (i j : ι) :
    ((h.mapIdZero F).mapIdZero G).hom i j = (h.mapIdZero (F ⋙ G)).hom i j := rfl

end Homotopy

namespace HomologicalComplex.Splitting

universe u v w uD vD

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {D : Type uD} [Category.{vD} D] [Preadditive D]
  {ι : Type w} {c : ComplexShape ι} {K : HomologicalComplex C c}

/-- Map the existing normalized contraction through the native additive homotopy functor. -/
noncomputable def mappedContractingHomotopy (s : Splitting K) (hK : K.Acyclic)
    (F : C ⥤ D) [F.Additive] :
    Homotopy (𝟙 ((F.mapHomologicalComplex c).obj K)) 0 :=
  (s.contractingHomotopy hK).mapIdZero F

/-- The mapped contraction uses exactly the functor image of the original normalized inverse. -/
@[simp]
lemma mappedContractingHomotopy_hom (s : Splitting K) (hK : K.Acyclic)
    (F : C ⥤ D) [F.Additive] (i j : ι) :
    (s.mappedContractingHomotopy hK F).hom i j = F.map (s.normalize.hom i j) := rfl

/-- An additive functor preserves exactness of a split exact complex at any mapped homology degree. -/
lemma exact_map_at_of_additive (s : Splitting K) (hK : K.Acyclic)
    (F : C ⥤ D) [F.Additive] (i : ι)
    [((F.mapHomologicalComplex c).obj K).HasHomology i] :
    (((F.mapHomologicalComplex c).obj K).sc i).Exact :=
  exactAt_of_homotopy_id_zero (s.mappedContractingHomotopy hK F) i

/-- Pointwise mapped homology turns the native mapped contraction into acyclicity. -/
lemma acyclic_map_of_additive (s : Splitting K) (hK : K.Acyclic)
    (F : C ⥤ D) [F.Additive]
    [∀ i, ((F.mapHomologicalComplex c).obj K).HasHomology i] :
    ((F.mapHomologicalComplex c).obj K).Acyclic :=
  fun i => s.exact_map_at_of_additive hK F i

/-- Any actual target acyclicity proof gives the same mapped normalized contraction components. -/
lemma contractingHomotopy_map_hom_of_target (s : Splitting K) (hK : K.Acyclic)
    (F : C ⥤ D) [F.Additive]
    (hL : ((F.mapHomologicalComplex c).obj K).Acyclic) (i j : ι) :
    ((s.map F).contractingHomotopy hL).hom i j =
      F.map ((s.contractingHomotopy hK).hom i j) := by
  rw [contractingHomotopy_hom, map_normalize, map_hom, contractingHomotopy_hom]

/-- The earned weak additive transport retains the native normalized contraction components. -/
lemma contractingHomotopy_map_hom_of_additive (s : Splitting K) (hK : K.Acyclic)
    (F : C ⥤ D) [F.Additive]
    [∀ i, ((F.mapHomologicalComplex c).obj K).HasHomology i] (i j : ι) :
    ((s.map F).contractingHomotopy (s.acyclic_map_of_additive hK F)).hom i j =
      F.map ((s.contractingHomotopy hK).hom i j) :=
  s.contractingHomotopy_map_hom_of_target hK F (s.acyclic_map_of_additive hK F) i j

/-- The earned native contracting components commute with additive functor transport. -/
lemma contractingHomotopy_map_hom (s : Splitting K) (hK : K.Acyclic)
    (F : C ⥤ D) [F.Additive]
    [∀ i, F.PreservesLeftHomologyOf (K.sc i)]
    [∀ i, F.PreservesRightHomologyOf (K.sc i)] (i j : ι) :
    ((s.map F).contractingHomotopy (acyclic_map_of_preservesHomologyOf hK F)).hom i j =
      F.map ((s.contractingHomotopy hK).hom i j) := by
  exact s.contractingHomotopy_map_hom_of_target hK F
    (acyclic_map_of_preservesHomologyOf hK F) i j

end HomologicalComplex.Splitting

namespace HomologicalComplex

universe u v w uD vD

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {D : Type uD} [Category.{vD} D] [Preadditive D]
  {ι : Type w} {c : ComplexShape ι} {K : HomologicalComplex C c}

/-- Split exactness survives every additive functor once the mapped complex has pointwise homology. -/
lemma IsSplitExact.map_of_additive (hK : IsSplitExact K) (F : C ⥤ D) [F.Additive]
    [∀ i, ((F.mapHomologicalComplex c).obj K).HasHomology i] :
    IsSplitExact ((F.mapHomologicalComplex c).obj K) := by
  rcases hK with ⟨⟨s⟩, hA⟩
  exact ⟨⟨s.map F⟩, s.acyclic_map_of_additive hA F⟩

end HomologicalComplex
