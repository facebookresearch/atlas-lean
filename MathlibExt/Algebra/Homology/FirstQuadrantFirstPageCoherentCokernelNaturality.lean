/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantFirstPageColumnNaturality
public import
  MathlibExt.Algebra.Homology.FirstQuadrantFirstPageDifferential
public import
  MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationFiniteComparison

/-!
# Naturality of the first-page column cokernel in coherent windows

Let K,L be nonnegative homological bicomplexes. In a preadditive category
with a zero object and finite coproducts, a bicomplex map f : K → L
commutes with projection of F_p Tot(K) onto its top column p.
After reindexing total chain degree n to cochain degree −n, the finite
and complete-stage projections are related by the complete-to-finite
stage comparison, and both projection squares commute with f.

For abelian C, choose the coherent first-page lower endpoint
ℓ_0=−1 and ℓ_(p+1)=p, with upper endpoint p. Let
t_p : F_(ℓ_p) → F_p be this window map and Q_p=coker(t_p).
The map f induces Q_p(K) → Q_p(L), and the comparison
Φ_p : Q_p ≅ D_p with the signed direct column is natural:
Φ_(L,p) ∘ Q_p(f) = D_p(f) ∘ Φ_(K,p).
Its projection equation is Φ_p ∘ π_p = Π_p, the complete-stage
top-column projection. The category object and morphism worlds
are independent.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

section Projection

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

omit [HasZeroObject C] in
/-- For a nonnegative homological bicomplex map f : K → L
in a preadditive category with finite coproducts, the degree p+q
stage-p map satisfies
P_(L,p,q) ∘ F_p(f)_(p+q) = f_(p,q) ∘ P_(K,p,q).
Here P_(p,q) projects F_p T_(p+q) onto its top column term K_(p,q). -/
@[reassoc]
theorem horizontalFilteredTotalMapOfBicomplex_topProjection
    (f : K ⟶ L) (p q : ℕ) :
    horizontalFilteredTotalMapOfBicomplex f p (p + q) ≫
        horizontalFilteredTopProjection L p q =
      horizontalFilteredTopProjection K p q ≫ (f.f p).f q := by
  apply Sigma.hom_ext
  intro idx
  change horizontalFilteredTotalι K p (p + q) idx ≫
      (horizontalFilteredTotalMapOfBicomplex f p (p + q) ≫
        horizontalFilteredTopProjection L p q) =
    horizontalFilteredTotalι K p (p + q) idx ≫
      (horizontalFilteredTopProjection K p q ≫ (f.f p).f q)
  simp only [← Category.assoc,
    horizontalFilteredTotalι_mapOfBicomplex,
    horizontalFilteredTotalι_topProjection]
  split_ifs with h
  · subst idx
    rw [Category.assoc, horizontalFilteredTopι_topProjection,
      Category.comp_id]
    dsimp [horizontalFilteredTopIndex]
    simp
  · rw [Category.assoc,
      horizontalFilteredTotalι_topProjection,
      dite_eq_right h, comp_zero, zero_comp]

/-- For a nonnegative homological bicomplex map f : K → L
in a preadditive category with a zero object and finite coproducts,
the extended finite-stage projection in degree i=−p−q satisfies
Π_L^i ∘ extend(F_p(f))^i = D_p(f)^i ∘ Π_K^i.
The maps use the supported column term K_(p,q) and its
signed direct-column presentation. -/
@[reassoc]
theorem horizontalNaturalDirectColumnProjectionComponent_naturality
    (f : K ⟶ L) (p q : ℕ) :
    (HomologicalComplex.extendMap
          (horizontalFilteredTotalComplexMapOfBicomplex f p)
          ComplexShape.embeddingDownNat).f (-(p : ℤ) - q) ≫
        horizontalNaturalDirectColumnProjectionComponent L p q =
      horizontalNaturalDirectColumnProjectionComponent K p q ≫
        (horizontalDirectColumnCochainMap f p).f (-(p : ℤ) - q) := by
  dsimp [horizontalNaturalDirectColumnProjectionComponent]
  rw [HomologicalComplex.extendMap_f
    (K := horizontalFilteredTotalComplex K p)
    (L := horizontalFilteredTotalComplex L p)
    (φ := horizontalFilteredTotalComplexMapOfBicomplex f p)
    (e := ComplexShape.embeddingDownNat)
    (i := p + q) (i' := -(p : ℤ) - q)
    (by rw [ComplexShape.embeddingDownNat_f]; push_cast; omega)]
  rw [horizontalDirectColumnCochainMap_f]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  dsimp only [horizontalFilteredTotalComplexMapOfBicomplex]
  change _ ≫ horizontalFilteredTotalMapOfBicomplex f p (p + q) ≫
      horizontalFilteredTopProjection L p q ≫ _ =
    _ ≫ horizontalFilteredTopProjection K p q ≫
      (f.f p).f q ≫ _
  slice_lhs 2 3 =>
    rw [horizontalFilteredTotalMapOfBicomplex_topProjection]
  simp only [Category.assoc]

/-- For f : K → L between nonnegative homological bicomplexes
in a preadditive category with a zero object and finite coproducts,
the finite-stage top-column projection satisfies
Π_L ∘ extend(F_p(f)) = D_p(f) ∘ Π_K as cochain maps.
The target direct column is supported in degrees i≤−p. -/
@[reassoc]
theorem horizontalNaturalDirectColumnProjectionMap_naturality
    (f : K ⟶ L) (p : ℕ) :
    HomologicalComplex.extendMap
          (horizontalFilteredTotalComplexMapOfBicomplex f p)
          ComplexShape.embeddingDownNat ≫
        horizontalNaturalDirectColumnProjectionMap L p =
      horizontalNaturalDirectColumnProjectionMap K p ≫
        horizontalDirectColumnCochainMap f p := by
  apply HomologicalComplex.Hom.ext
  funext i
  change
    (HomologicalComplex.extendMap
          (horizontalFilteredTotalComplexMapOfBicomplex f p)
          ComplexShape.embeddingDownNat).f i ≫
        horizontalNaturalDirectColumnProjection L p i =
      horizontalNaturalDirectColumnProjection K p i ≫
        (horizontalDirectColumnCochainMap f p).f i
  by_cases hi : -(p : ℤ) < i
  · rw [horizontalNaturalDirectColumnProjection_eq_zero_of_lt L p i hi,
      horizontalNaturalDirectColumnProjection_eq_zero_of_lt K p i hi,
      comp_zero, zero_comp]
  · have hile : i ≤ -(p : ℤ) := by lia
    obtain ⟨q, rfl⟩ : ∃ q : ℕ, i = -(p : ℤ) - q :=
      ⟨horizontalColumnDegree p i,
        horizontalColumnDegree_spec p i hile⟩
    rw [horizontalNaturalDirectColumnProjection_eq_component,
      horizontalNaturalDirectColumnProjection_eq_component]
    exact horizontalNaturalDirectColumnProjectionComponent_naturality
      f p q

set_option linter.flexible false in
/-- For a nonnegative homological bicomplex K in a preadditive
category with a zero object and finite coproducts, the cochain
comparison from complete stage F_p to the finite stage with
columns a≤p is the extension of their chain-level comparison.
It reindexes total degree n to cochain degree −n. -/
theorem horizontalCompleteFiltrationCochainUpperIso_hom_eq_finite
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p : ℕ) :
    (horizontalCompleteFiltrationCochainUpperIso K p).hom =
      HomologicalComplex.extendMap
        (horizontalCompleteFilteredTotalComplexFiniteIso K (p : ℤ)
          (by omega)).hom ComplexShape.embeddingDownNat := by
  apply HomologicalComplex.Hom.ext
  funext i
  simp [horizontalCompleteFiltrationCochainUpperIso,
    horizontalCompleteFiltrationCochainMonoUpperIso,
    horizontalCompleteFilteredTotalMonoOverUpperIso,
    horizontalCompleteFilteredTotalComplexFiniteIso]
  exact HomologicalComplex.extendMap_id_f
    ((horizontalCompleteFilteredTotalMonoOver K
      (horizontalFirstPageUpperIndex p)).obj.left)
    ComplexShape.embeddingDownNat i

/-- For a nonnegative homological bicomplex K in a preadditive
category with a zero object and finite coproducts, let α_p compare
the complete stage F_p to its finite-stage cochain presentation.
Then Π_p^complete = Π_p^finite ∘ α_p as maps to D_p.
The equality includes the zero-column stage p=0. -/
theorem horizontalCompleteDirectColumnProjectionMap_eq_finite
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p : ℕ) :
    horizontalCompleteDirectColumnProjectionMap K p =
      HomologicalComplex.extendMap
          (horizontalCompleteFilteredTotalComplexFiniteIso K (p : ℤ)
            (by omega)).hom ComplexShape.embeddingDownNat ≫
        horizontalNaturalDirectColumnProjectionMap K p := by
  rw [← horizontalCompleteFiltrationCochainUpperIso_hom_eq_finite]
  cases p with
  | zero =>
      apply HomologicalComplex.Hom.ext
      funext i
      change horizontalDirectColumnProjection K 0 i =
        (horizontalCompleteFiltrationCochainUpperIso K 0).hom.f i ≫
          horizontalNaturalDirectColumnProjection K 0 i
      by_cases hi : (0 : ℤ) < i
      · rw [horizontalDirectColumnProjection_eq_zero_of_lt K 0 i hi,
          horizontalNaturalDirectColumnProjection_eq_zero_of_lt K 0 i hi,
          comp_zero]
      · have hile : i ≤ (0 : ℤ) := by lia
        obtain ⟨q, rfl⟩ : ∃ q : ℕ, i = -(0 : ℤ) - q :=
          ⟨horizontalColumnDegree 0 i,
            horizontalColumnDegree_spec 0 i hile⟩
        have hile' : -(0 : ℤ) - q ≤ -((0 : ℕ) : ℤ) := by omega
        unfold horizontalDirectColumnProjection
        rw [dite_eq_left hile']
        unfold horizontalNaturalDirectColumnProjection
        rw [dite_eq_left hile']
        simp [horizontalColumnDegree,
          horizontalDirectColumnProjectionComponent,
          horizontalNaturalDirectColumnProjectionComponent,
          Category.assoc]
  | succ p =>
      simp [horizontalCompleteDirectColumnProjectionMap,
        horizontalCompleteSuccDirectColumnProjectionMap,
        horizontalMonoStageDirectColumnProjectionMap,
        horizontalNaturalStageCochainIso,
        horizontalCompleteFiltrationCochainUpperIso,
        horizontalCompleteFiltrationCochainMonoUpperIso,
        horizontalCompleteFiltrationCochainMonoUpperSuccIso,
        horizontalCompleteFilteredTotalMonoOverUpperIso,
        horizontalCompleteFilteredTotalMonoOverUpperSuccIso]

/-- For f : K → L between nonnegative homological bicomplexes
in a preadditive category with a zero object and finite coproducts,
the complete projections satisfy
Π_(L,p) ∘ F_p^complete(f) = D_p(f) ∘ Π_(K,p).
All maps are integer cochain maps at the upper stage p. -/
@[reassoc]
theorem horizontalCompleteDirectColumnProjectionMap_naturality
    (f : K ⟶ L) (p : ℕ) :
    HomologicalComplex.extendMap
          (horizontalCompleteFilteredTotalComplexMapOfBicomplex f
            (horizontalFirstPageUpperIndex p))
          ComplexShape.embeddingDownNat ≫
        horizontalCompleteDirectColumnProjectionMap L p =
      horizontalCompleteDirectColumnProjectionMap K p ≫
        horizontalDirectColumnCochainMap f p := by
  rw [horizontalCompleteDirectColumnProjectionMap_eq_finite,
    horizontalCompleteDirectColumnProjectionMap_eq_finite]
  have hFinite :=
    horizontalCompleteFilteredTotalComplexFiniteIso_naturality f
      (p : ℤ) (by omega)
  have hFiniteExt := congrArg
    (fun k ↦ HomologicalComplex.extendMap k
      ComplexShape.embeddingDownNat) hFinite
  simp only [HomologicalComplex.extendMap_comp] at hFiniteExt
  have hFiniteExt' :
      HomologicalComplex.extendMap
            (horizontalCompleteFilteredTotalComplexFiniteIso K (p : ℤ)
              (by omega)).hom ComplexShape.embeddingDownNat ≫
          HomologicalComplex.extendMap
            (horizontalFilteredTotalComplexMapOfBicomplex f p)
            ComplexShape.embeddingDownNat =
        HomologicalComplex.extendMap
            (horizontalCompleteFilteredTotalComplexMapOfBicomplex f
              ((p : ℤ) : EInt)) ComplexShape.embeddingDownNat ≫
          HomologicalComplex.extendMap
            (horizontalCompleteFilteredTotalComplexFiniteIso L (p : ℤ)
              (by omega)).hom ComplexShape.embeddingDownNat := by
    simpa using hFiniteExt
  unfold horizontalFirstPageUpperIndex
  calc
    _ = (HomologicalComplex.extendMap
          (horizontalCompleteFilteredTotalComplexMapOfBicomplex f
            ((p : ℤ) : EInt)) ComplexShape.embeddingDownNat ≫
        HomologicalComplex.extendMap
          (horizontalCompleteFilteredTotalComplexFiniteIso L (p : ℤ)
            (by omega)).hom ComplexShape.embeddingDownNat) ≫
        horizontalNaturalDirectColumnProjectionMap L p :=
      (Category.assoc _ _ _).symm
    _ = (HomologicalComplex.extendMap
          (horizontalCompleteFilteredTotalComplexFiniteIso K (p : ℤ)
            (by omega)).hom ComplexShape.embeddingDownNat ≫
        HomologicalComplex.extendMap
          (horizontalFilteredTotalComplexMapOfBicomplex f p)
          ComplexShape.embeddingDownNat) ≫
        horizontalNaturalDirectColumnProjectionMap L p := by
      rw [hFiniteExt']
    _ = HomologicalComplex.extendMap
          (horizontalCompleteFilteredTotalComplexFiniteIso K (p : ℤ)
            (by omega)).hom ComplexShape.embeddingDownNat ≫
        (HomologicalComplex.extendMap
          (horizontalFilteredTotalComplexMapOfBicomplex f p)
          ComplexShape.embeddingDownNat ≫
        horizontalNaturalDirectColumnProjectionMap L p) :=
      Category.assoc _ _ _
    _ = HomologicalComplex.extendMap
          (horizontalCompleteFilteredTotalComplexFiniteIso K (p : ℤ)
            (by omega)).hom ComplexShape.embeddingDownNat ≫
        (horizontalNaturalDirectColumnProjectionMap K p ≫
          horizontalDirectColumnCochainMap f p) := by
      rw [horizontalNaturalDirectColumnProjectionMap_naturality]
    _ = (HomologicalComplex.extendMap
          (horizontalCompleteFilteredTotalComplexFiniteIso K (p : ℤ)
            (by omega)).hom ComplexShape.embeddingDownNat ≫
        horizontalNaturalDirectColumnProjectionMap K p) ≫
        horizontalDirectColumnCochainMap f p :=
      (Category.assoc _ _ _).symm

end Projection

section Coherent

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- For a nonnegative homological bicomplex map f : K → L
in an abelian category, the map on the coherent lower cochain
endpoint is F_(ℓ_p)(f), with ℓ_0=−1 and ℓ_(p+1)=p.
It is the extension of the complete filtered chain map to
cochain degrees −n. -/
noncomputable abbrev horizontalFirstPageCoherentLowerCochainMapOfBicomplex
    (f : K ⟶ L) (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageCoherentLowerIndex p) ⟶
      (horizontalCompleteFiltrationCochainDiagram L).obj
        (horizontalFirstPageCoherentLowerIndex p) :=
  HomologicalComplex.extendMap
    (horizontalCompleteFilteredTotalComplexMapOfBicomplex f
      (horizontalFirstPageCoherentLowerIndex p))
    ComplexShape.embeddingDownNat

/-- For a nonnegative homological bicomplex map f : K → L
in an abelian category, the upper endpoint map of the coherent
column-p window is F_p(f), reindexed as an integer cochain map.
The upper stage contains horizontal columns at most p. -/
noncomputable abbrev horizontalFirstPageCoherentUpperCochainMapOfBicomplex
    (f : K ⟶ L) (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex p) ⟶
      (horizontalCompleteFiltrationCochainDiagram L).obj
        (horizontalFirstPageUpperIndex p) :=
  HomologicalComplex.extendMap
    (horizontalCompleteFilteredTotalComplexMapOfBicomplex f
      (horizontalFirstPageUpperIndex p))
    ComplexShape.embeddingDownNat

/-- For f : K → L between nonnegative homological bicomplexes
in an abelian category, let t_p^K : F_(ℓ_p)(K) → F_p(K) and
t_p^L be the coherent window maps. They satisfy
F_p(f) ∘ t_p^K = t_p^L ∘ F_(ℓ_p)(f),
with ℓ_0=−1 and ℓ_(p+1)=p. -/
theorem horizontalFirstPageCoherentMap_naturality_of_bicomplex
    (f : K ⟶ L) (p : ℕ) :
    horizontalFirstPageCoherentMap K p ≫
        horizontalFirstPageCoherentUpperCochainMapOfBicomplex f p =
      horizontalFirstPageCoherentLowerCochainMapOfBicomplex f p ≫
        horizontalFirstPageCoherentMap L p := by
  have h :=
    horizontalCompleteFilteredTotalComplexMapOfBicomplex_naturality f
      (horizontalFirstPageCoherentIndex_le p)
  have hExt := congrArg
    (fun k ↦ HomologicalComplex.extendMap k
      ComplexShape.embeddingDownNat) h.symm
  simp only [HomologicalComplex.extendMap_comp] at hExt
  change
    HomologicalComplex.extendMap
          (horizontalCompleteFilteredTotalMap K
            (horizontalFirstPageCoherentIndex_le p))
          ComplexShape.embeddingDownNat ≫
        horizontalFirstPageCoherentUpperCochainMapOfBicomplex f p =
      horizontalFirstPageCoherentLowerCochainMapOfBicomplex f p ≫
        HomologicalComplex.extendMap
          (horizontalCompleteFilteredTotalMap L
            (horizontalFirstPageCoherentIndex_le p))
          ComplexShape.embeddingDownNat
  exact hExt

/-- For a nonnegative homological bicomplex map f : K → L
in an abelian category, the coherent endpoint square induces
Q_p(f) : coker(t_p^K) → coker(t_p^L).
Its lower and upper endpoint maps are F_(ℓ_p)(f) and F_p(f),
respectively, with ℓ_0=−1 and ℓ_(p+1)=p. -/
noncomputable def horizontalFirstPageCoherentCokernelMapOfBicomplex
    (f : K ⟶ L) (p : ℕ) :
    cokernel (horizontalFirstPageCoherentMap K p) ⟶
      cokernel (horizontalFirstPageCoherentMap L p) :=
  cokernel.map
    (horizontalFirstPageCoherentMap K p)
    (horizontalFirstPageCoherentMap L p)
    (horizontalFirstPageCoherentLowerCochainMapOfBicomplex f p)
    (horizontalFirstPageCoherentUpperCochainMapOfBicomplex f p)
    (horizontalFirstPageCoherentMap_naturality_of_bicomplex f p)

/-- For a nonnegative homological bicomplex map f : K → L
in an abelian category, the coherent cokernel projections satisfy
Q_p(f) ∘ π_K = π_L ∘ F_p(f).
This is the quotient square from the upper stage F_p(K)
to the coherent cokernel for L. -/
@[reassoc]
theorem horizontalFirstPageCoherentCokernelMapOfBicomplex_π
    (f : K ⟶ L) (p : ℕ) :
    cokernel.π (horizontalFirstPageCoherentMap K p) ≫
        horizontalFirstPageCoherentCokernelMapOfBicomplex f p =
      horizontalFirstPageCoherentUpperCochainMapOfBicomplex f p ≫
        cokernel.π (horizontalFirstPageCoherentMap L p) := by
  exact cokernel.π_desc _ _ _

/-- For a nonnegative homological bicomplex K in an abelian
category, the coherent cokernel isomorphism Φ_p : coker(t_p) ≅ D_p
satisfies Φ_p ∘ π_p = Π_p.
Here π_p is the cokernel projection from complete stage F_p,
and Π_p is the complete top-column projection. -/
@[reassoc]
theorem horizontalFirstPageCoherentCokernelIso_π_hom
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p : ℕ) :
    cokernel.π (horizontalFirstPageCoherentMap K p) ≫
        (horizontalFirstPageCoherentCokernelIso K p).hom =
      horizontalCompleteDirectColumnProjectionMap K p := by
  cases p with
  | zero =>
      change cokernel.π (horizontalFirstPageFiltrationMap K 0) ≫
          (horizontalFirstPageCokernelIso K 0).hom =
        horizontalCompleteDirectColumnProjectionMap K 0
      unfold horizontalFirstPageCokernelIso
        horizontalFirstPageCokernelToDirectColumn
      rw [cokernel.π_desc]
  | succ p =>
      change cokernel.π (horizontalFirstPageNextFiltrationMap K p) ≫
          (horizontalFirstPageAdjacentRightIso K p).hom =
        horizontalCompleteDirectColumnProjectionMap K (p + 1)
      dsimp [horizontalFirstPageAdjacentRightIso,
        horizontalFirstPageNextCokernelIso,
        horizontalFirstPageCokernelIso]
      rw [cokernel.mapIso_hom]
      rw [cokernel.π_desc_assoc]
      simp only [Iso.refl_hom, Category.id_comp]
      unfold horizontalFirstPageCokernelToDirectColumn
      rw [cokernel.π_desc]

/-- For a nonnegative homological bicomplex map f : K → L
in an abelian category, the coherent cokernel comparisons satisfy
Φ_(L,p) ∘ Q_p(f) = D_p(f) ∘ Φ_(K,p).
The source is coker(F_(ℓ_p)(K) → F_p(K)), the target is D_p(L),
and ℓ_0=−1, ℓ_(p+1)=p. -/
@[reassoc]
theorem horizontalFirstPageCoherentCokernelIso_hom_naturality_of_bicomplex
    (f : K ⟶ L) (p : ℕ) :
    horizontalFirstPageCoherentCokernelMapOfBicomplex f p ≫
        (horizontalFirstPageCoherentCokernelIso L p).hom =
      (horizontalFirstPageCoherentCokernelIso K p).hom ≫
        horizontalDirectColumnCochainMap f p := by
  apply (cancel_epi
    (cokernel.π (horizontalFirstPageCoherentMap K p))).1
  calc
    cokernel.π (horizontalFirstPageCoherentMap K p) ≫
        (horizontalFirstPageCoherentCokernelMapOfBicomplex f p ≫
          (horizontalFirstPageCoherentCokernelIso L p).hom) =
      (cokernel.π (horizontalFirstPageCoherentMap K p) ≫
        horizontalFirstPageCoherentCokernelMapOfBicomplex f p) ≫
          (horizontalFirstPageCoherentCokernelIso L p).hom :=
      (Category.assoc _ _ _).symm
    _ = (horizontalFirstPageCoherentUpperCochainMapOfBicomplex f p ≫
          cokernel.π (horizontalFirstPageCoherentMap L p)) ≫
        (horizontalFirstPageCoherentCokernelIso L p).hom := by
      rw [horizontalFirstPageCoherentCokernelMapOfBicomplex_π]
    _ = horizontalFirstPageCoherentUpperCochainMapOfBicomplex f p ≫
        (cokernel.π (horizontalFirstPageCoherentMap L p) ≫
          (horizontalFirstPageCoherentCokernelIso L p).hom) :=
      Category.assoc _ _ _
    _ = horizontalFirstPageCoherentUpperCochainMapOfBicomplex f p ≫
        horizontalCompleteDirectColumnProjectionMap L p := by
      rw [horizontalFirstPageCoherentCokernelIso_π_hom]
    _ = horizontalCompleteDirectColumnProjectionMap K p ≫
        horizontalDirectColumnCochainMap f p :=
      horizontalCompleteDirectColumnProjectionMap_naturality f p
    _ = (cokernel.π (horizontalFirstPageCoherentMap K p) ≫
          (horizontalFirstPageCoherentCokernelIso K p).hom) ≫
        horizontalDirectColumnCochainMap f p := by
      rw [horizontalFirstPageCoherentCokernelIso_π_hom]
    _ = cokernel.π (horizontalFirstPageCoherentMap K p) ≫
        ((horizontalFirstPageCoherentCokernelIso K p).hom ≫
          horizontalDirectColumnCochainMap f p) :=
      Category.assoc _ _ _

end Coherent

end HomologicalComplex₂

end
