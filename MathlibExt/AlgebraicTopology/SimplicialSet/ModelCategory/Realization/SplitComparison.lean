/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.SplitComposite
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.ContinuousWhitehead
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveEquivalenceWeakEquivalence

/-!
# Homotopy sections and weak composites of realizations

A homotopy section and a homotopy equivalence of a composite give an explicit
homotopy equivalence of the first map. For simplicial realizations the
canonical continuous Whitehead theorem derives the composite equivalence.
The section and kernel-composite homotopies then transfer a weak comparison
map to the first map and its comparison composite.
-/

universe u v w k

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace SSet.RealizationCWUpgrade

open CategoryTheory

/-- For actual realizations, composite weakness supplies the required composite HE.
The original homotopy section gives an explicit inverse for realization of f. -/
def splitCompositeRealizationEquiv {A B C : SSet.{k}}
    (f : A ⟶ B) (g : B ⟶ C) (i : B ⟶ A)
    (hComposite : SSet.realizationWeakEquivalences (f ≫ g))
    (hSection : SSet.Homotopy (i ≫ f) (𝟙 B)) :
    ContinuousMap.HomotopyEquiv (SSet.toTop.obj A) (SSet.toTop.obj B) := by
  let ft := (SSet.toTop.map f).hom
  let gt := (SSet.toTop.map g).hom
  let it := (SSet.toTop.map i).hom
  let e := realizationHomotopyEquiv (f ≫ g) hComposite
  have he : e.toFun = gt.comp ft := by
    rewrite [realizationHomotopyEquiv_toFun, SSet.toTop.map_comp]
    rfl
  let H := SSet.realizeHomotopy B B (i ≫ f) (𝟙 B) hSection
  have hLeft : (SSet.toTop.map (i ≫ f)).hom = ft.comp it := by
    rewrite [SSet.toTop.map_comp]
    rfl
  have hRight : (SSet.toTop.map (𝟙 B)).hom = ContinuousMap.id (SSet.toTop.obj B) := by
    rewrite [SSet.toTop.map_id]
    rfl
  exact ContinuousMap.splitCompositeHomotopyEquiv ft gt it e he (H.cast hLeft hRight)

/-- Composite weakness and the ACTUAL homotopy section imply weakness of the first map.
This does not supply the antecedent composite/J geometric gate. -/
theorem realizationWeakEquivalence_of_splitComposite {A B C : SSet.{k}}
    (f : A ⟶ B) (g : B ⟶ C) (i : B ⟶ A)
    (hComposite : SSet.realizationWeakEquivalences (f ≫ g))
    (hSection : SSet.Homotopy (i ≫ f) (𝟙 B)) : SSet.realizationWeakEquivalences f := by
  change TopCat.weakHomotopyEquivalences (SSet.toTop.map f)
  exact TopCat.mem_of_eq_toFun (splitCompositeRealizationEquiv f g i hComposite hSection) rfl

private theorem realization_mem_of_identity_homotopy {A : SSet.{k}}
    (f : A ⟶ A) (H : SSet.Homotopy f (𝟙 A)) : SSet.realizationWeakEquivalences f := by
  let ht := SSet.realizeHomotopy A A f (𝟙 A) H
  have hid : (SSet.toTop.map (𝟙 A)).hom = ContinuousMap.id (SSet.toTop.obj A) := by
    rewrite [SSet.toTop.map_id]
    rfl
  let h := ht.cast rfl hid
  let e : ContinuousMap.HomotopyEquiv (SSet.toTop.obj A) (SSet.toTop.obj A) :=
    { toFun := (SSet.toTop.map f).hom
      invFun := ContinuousMap.id (SSet.toTop.obj A)
      left_inv := by exact ⟨h⟩
      right_inv := by exact ⟨h⟩ }
  change TopCat.weakHomotopyEquivalences (SSet.toTop.map f)
  exact TopCat.mem_of_eq_toFun e rfl

/-- Conditional comparison consequence: the ACTUAL J weakness, section homotopy
and kernel-composite identity homotopy give weakness of Gamma's map.
No geometric J proof or finished Gamma/eta weakness is supplied by this lemma. -/
theorem realizationWeakEquivalence_of_section_comparison {N V K : SSet.{k}}
    (gamma : N ⟶ V) (kappa : V ⟶ K) (i : V ⟶ N) (j : K ⟶ N)
    (hJ : SSet.realizationWeakEquivalences j)
    (hSection : SSet.Homotopy (i ≫ gamma) (𝟙 V))
    (hKernel : SSet.Homotopy (j ≫ gamma ≫ kappa) (𝟙 K)) :
    SSet.realizationWeakEquivalences gamma := by
  have hTotal : SSet.realizationWeakEquivalences (j ≫ (gamma ≫ kappa)) :=
    realization_mem_of_identity_homotopy (j ≫ gamma ≫ kappa) hKernel
  have hComposite : SSet.realizationWeakEquivalences (gamma ≫ kappa) :=
    SSet.realizationWeakEquivalences.of_precomp j (gamma ≫ kappa) hJ hTotal
  exact realizationWeakEquivalence_of_splitComposite gamma kappa i hComposite hSection

/-- The original comparison J followed by Gamma is weak under the same explicit
geometric antecedent and full map homotopies; no eta result premise appears. -/
theorem realizationWeakEquivalence_of_comparison_composite {N V K : SSet.{k}}
    (gamma : N ⟶ V) (kappa : V ⟶ K) (i : V ⟶ N) (j : K ⟶ N)
    (hJ : SSet.realizationWeakEquivalences j)
    (hSection : SSet.Homotopy (i ≫ gamma) (𝟙 V))
    (hKernel : SSet.Homotopy (j ≫ gamma ≫ kappa) (𝟙 K)) :
    SSet.realizationWeakEquivalences (j ≫ gamma) :=
  SSet.realizationWeakEquivalences.comp_mem j gamma hJ
    (realizationWeakEquivalence_of_section_comparison gamma kappa i j hJ hSection hKernel)

end SSet.RealizationCWUpgrade
