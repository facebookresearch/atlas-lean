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
# Functorial transport of split exact complexes

Zero-preserving functors preserve split exactness when they preserve the
left and right homology constructions of each degreewise short complex.
An additive functor also maps a contracting homotopy directly; this gives
exactness wherever the mapped complex has homology, without a global
exactness assumption on the functor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HomologicalComplex

universe u v w uD vD

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D]
  {ι : Type w} {c : ComplexShape ι} {K : HomologicalComplex C c}

/--
Let C,D have zero morphisms, let K be a c-complex and F:C⥤D preserve zero morphisms. For a
degree i, write Sᵢ=(K_prev(i)→Kᵢ→K_next(i)). Assume K has homology at i and F preserves both
the left and right homology constructions of Sᵢ. Then the mapped complex F(K) has homology at
i.
-/
lemma hasHomology_map_of_preservesHomologyOf (K : HomologicalComplex C c)
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (i : ι) [K.HasHomology i]
    [F.PreservesLeftHomologyOf (K.sc i)] [F.PreservesRightHomologyOf (K.sc i)] :
    ((F.mapHomologicalComplex c).obj K).HasHomology i := by
  change ((K.sc i).map F).HasHomology
  infer_instance

/--
Let C,D have zero morphisms, let K be a c-complex and F:C⥤D preserve zero morphisms. For a
degree i, write Sᵢ=(K_prev(i)→Kᵢ→K_next(i)). If K is acyclic and F preserves both left and
right homology of every Sᵢ, then F(K) is acyclic.
-/
lemma acyclic_map_of_preservesHomologyOf (hK : K.Acyclic) (F : C ⥤ D)
    [F.PreservesZeroMorphisms]
    [∀ i, F.PreservesLeftHomologyOf (K.sc i)]
    [∀ i, F.PreservesRightHomologyOf (K.sc i)] :
    ((F.mapHomologicalComplex c).obj K).Acyclic := by
  intro i
  change ((K.sc i).map F).Exact
  exact (hK i).map F

/--
Let C,D have zero morphisms, let K be a c-complex and F:C⥤D preserve zero morphisms. For a
degree i, write Sᵢ=(K_prev(i)→Kᵢ→K_next(i)). If K is split exact and F preserves left and
right homology of every Sᵢ, then F(K) is split exact: map the splitting and the degreewise
exactness.
-/
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

/--
Let C,D be preadditive categories, K a c-complex, and F:C⥤D an additive functor. A contracting
homotopy H:1_K∼0 maps to a contracting homotopy 1_{F(K)}∼0 with components F(H.hom i j).
-/
noncomputable def mapIdZero (h : Homotopy (𝟙 K) 0) (F : C ⥤ D) [F.Additive] :
    Homotopy (𝟙 ((F.mapHomologicalComplex c).obj K)) 0 where
  hom := (F.mapHomotopy h).hom
  zero := (F.mapHomotopy h).zero
  comm i := by
    have hId := HomologicalComplex.congr_hom ((F.mapHomologicalComplex c).map_id K) i
    exact hId.symm.trans (by
      simpa only [Functor.map_zero] using (F.mapHomotopy h).comm i)

/--
Let C,D be preadditive categories, K a c-complex, and F:C⥤D an additive functor. For H:1_K∼0,
the degree-(i,j) component of its mapped contraction is F.map(H.hom i j).
-/
@[simp]
lemma mapIdZero_hom (h : Homotopy (𝟙 K) 0) (F : C ⥤ D) [F.Additive] (i j : ι) :
    (h.mapIdZero F).hom i j = F.map (h.hom i j) := rfl

/--
Let K be a c-complex in a preadditive category C and H:1_K∼0 a contraction. Mapping H by the
identity functor leaves every component unchanged: (H.mapIdZero(𝟭C)).hom i j=H.hom i j.
-/
lemma mapIdZero_id_hom (h : Homotopy (𝟙 K) 0) (i j : ι) :
    (h.mapIdZero (𝟭 C)).hom i j = h.hom i j := rfl

/--
Let C,D,E be preadditive categories, F:C⥤D and G:D⥤E additive, and H:1_K∼0 a contraction of a
c-complex K in C. Mapping first by F then by G has the same components as mapping by F⋙G.
-/
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

/--
Let C,D be preadditive categories, K a c-complex, and F:C⥤D an additive functor. Let s be a
splitting of K and assume K is acyclic. The normalized contraction with components
s.normalize.hom maps to a homotopy 1_{F(K)}∼0. No mapped homology existence is needed to
construct this homotopy.
-/
noncomputable def mappedContractingHomotopy (s : Splitting K) (hK : K.Acyclic)
    (F : C ⥤ D) [F.Additive] :
    Homotopy (𝟙 ((F.mapHomologicalComplex c).obj K)) 0 :=
  (s.contractingHomotopy hK).mapIdZero F

/--
Let C,D be preadditive categories, K a c-complex, and F:C⥤D an additive functor. Let s be a
splitting of K and assume K is acyclic. The mapped contraction has component
F.map(s.normalize.hom i j) in reversed degree (i,j).
-/
@[simp]
lemma mappedContractingHomotopy_hom (s : Splitting K) (hK : K.Acyclic)
    (F : C ⥤ D) [F.Additive] (i j : ι) :
    (s.mappedContractingHomotopy hK F).hom i j = F.map (s.normalize.hom i j) := rfl

/--
Let C,D be preadditive categories, K a c-complex, and F:C⥤D an additive functor. Let s be a
splitting of K and assume K is acyclic. If F(K) has homology at degree i, its three-term
complex around i is exact, as a consequence of the mapped contraction.
-/
lemma exact_map_at_of_additive (s : Splitting K) (hK : K.Acyclic)
    (F : C ⥤ D) [F.Additive] (i : ι)
    [((F.mapHomologicalComplex c).obj K).HasHomology i] :
    (((F.mapHomologicalComplex c).obj K).sc i).Exact :=
  exactAt_of_homotopy_id_zero (s.mappedContractingHomotopy hK F) i

/--
Let C,D be preadditive categories, K a c-complex, and F:C⥤D an additive functor. Let s be a
splitting of K and assume K is acyclic. If F(K) has homology at every degree, the mapped
contraction makes F(K) acyclic.
-/
lemma acyclic_map_of_additive (s : Splitting K) (hK : K.Acyclic)
    (F : C ⥤ D) [F.Additive]
    [∀ i, ((F.mapHomologicalComplex c).obj K).HasHomology i] :
    ((F.mapHomologicalComplex c).obj K).Acyclic :=
  fun i => s.exact_map_at_of_additive hK F i

/--
Let C,D be preadditive categories, K a c-complex, and F:C⥤D an additive functor. Let s be a
splitting of K and assume K is acyclic. Assume additionally that F(K) is acyclic. The
normalized contraction of the mapped splitting has the same component as F of the original
contraction: H_{s.map F}.hom i j=F(H_s.hom i j).
-/
lemma contractingHomotopy_map_hom_of_target (s : Splitting K) (hK : K.Acyclic)
    (F : C ⥤ D) [F.Additive]
    (hL : ((F.mapHomologicalComplex c).obj K).Acyclic) (i j : ι) :
    ((s.map F).contractingHomotopy hL).hom i j =
      F.map ((s.contractingHomotopy hK).hom i j) := by
  rw [contractingHomotopy_hom, map_normalize, map_hom, contractingHomotopy_hom]

/--
Let C,D be preadditive categories, K a c-complex, and F:C⥤D an additive functor. Let s be a
splitting of K and assume K is acyclic. Assume F(K) has homology in every degree, so its
acyclicity follows from the mapped contraction. Its normalized contracting components are F of
the original normalized contracting components.
-/
lemma contractingHomotopy_map_hom_of_additive (s : Splitting K) (hK : K.Acyclic)
    (F : C ⥤ D) [F.Additive]
    [∀ i, ((F.mapHomologicalComplex c).obj K).HasHomology i] (i j : ι) :
    ((s.map F).contractingHomotopy (s.acyclic_map_of_additive hK F)).hom i j =
      F.map ((s.contractingHomotopy hK).hom i j) :=
  s.contractingHomotopy_map_hom_of_target hK F (s.acyclic_map_of_additive hK F) i j

/--
Let C,D be preadditive categories, K a c-complex, and F:C⥤D an additive functor. Let s be a
splitting of K and assume K is acyclic. Assume F preserves both left and right homology of
every Sᵢ=(K_prev(i)→Kᵢ→K_next(i)). The induced acyclicity of F(K) identifies its normalized
contraction component with F of the corresponding component of K.
-/
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

/--
Let C,D be preadditive categories, K a c-complex, and F:C⥤D an additive functor. If K is split
exact and F(K) has homology at every degree, then F(K) is split exact. The additive image of a
contraction provides the needed splitting and exactness.
-/
lemma IsSplitExact.map_of_additive (hK : IsSplitExact K) (F : C ⥤ D) [F.Additive]
    [∀ i, ((F.mapHomologicalComplex c).obj K).HasHomology i] :
    IsSplitExact ((F.mapHomologicalComplex c).obj K) := by
  rcases hK with ⟨⟨s⟩, hA⟩
  exact ⟨⟨s.map F⟩, s.acyclic_map_of_additive hA F⟩

end HomologicalComplex
