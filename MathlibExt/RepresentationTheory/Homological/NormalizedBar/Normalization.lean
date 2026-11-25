/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.Degeneracies
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import MathlibExt.RepresentationTheory.Homological.NormalizedBar.Basic

/-!
# The literal normalized group bar complex

The native normalized Moore complex of the linearized universal cover is
identified degreewise with the free representation on nonidentity tuples.
The differential is transported through these actual inverse degree maps.
The canonical projection deletes degenerate symbols, while its chain
section applies the native normalization projector to raw tuple symbols.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial MonoidAlgebra DoldKan

universe u v

namespace Rep.NormalizedBar

variable (k : Type u) [CommRing k] (G : Type v) [Group G]

/-- Native Dold–Kan normalization of the actual linearized universal cover. -/
abbrev mooreComplex : ChainComplex (Rep.{max u v} k G) ℕ :=
  (AlgebraicTopology.normalizedMooreComplex _).obj (standardSimplicial k G)

/-- The actual native normalization map into the Moore complex. -/
abbrev normalize : standardComplex k G ⟶ mooreComplex k G :=
  AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex (standardSimplicial k G)

/-- The actual native inclusion of the Moore complex. -/
abbrev includeMoore : mooreComplex k G ⟶ standardComplex k G :=
  AlgebraicTopology.inclusionOfMooreComplexMap (standardSimplicial k G)

/-- The native projector on the alternating-face standard complex. -/
abbrev projector : standardComplex k G ⟶ standardComplex k G :=
  AlgebraicTopology.DoldKan.PInfty (X := standardSimplicial k G)

@[reassoc (attr := simp)]
theorem normalize_comp_includeMoore :
    normalize k G ≫ includeMoore k G = projector k G :=
  AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap
    (standardSimplicial k G)

@[reassoc (attr := simp)]
theorem includeMoore_comp_normalize :
    includeMoore k G ≫ normalize k G = 𝟙 (mooreComplex k G) :=
  (AlgebraicTopology.DoldKan.splitMonoInclusionOfMooreComplexMap (standardSimplicial k G)).id

@[reassoc]
theorem includeMoore_comp_projector :
    includeMoore k G ≫ projector k G = includeMoore k G :=
  AlgebraicTopology.DoldKan.inclusionOfMooreComplexMap_comp_PInfty (standardSimplicial k G)

@[reassoc]
theorem normalize_f_comp_includeMoore_f (n : ℕ) :
    (normalize k G).f n ≫ (includeMoore k G).f n = (projector k G).f n :=
  congrArg (fun f => f.f n) (normalize_comp_includeMoore k G)

@[reassoc]
theorem includeMoore_f_comp_normalize_f (n : ℕ) :
    (includeMoore k G).f n ≫ (normalize k G).f n = 𝟙 ((mooreComplex k G).X n) :=
  congrArg (fun f => f.f n) (includeMoore_comp_normalize k G)

@[reassoc]
theorem includeMoore_f_comp_projector_f (n : ℕ) :
    (includeMoore k G).f n ≫ (projector k G).f n = (includeMoore k G).f n :=
  congrArg (fun f => f.f n) (includeMoore_comp_projector k G)

/-- A homogeneous simplex with repeated adjacent entries has zero tuple projection. -/
theorem standardProjection_single_of_degenerate (n : ℕ) (a : Fin (n + 1) → G)
    (i : Fin n) (ha : a i.castSucc = a i.succ) (r : k) :
    (standardProjection k G n).hom (standardSymbol k G n a r) = 0 := by
  classical
  rw [standardProjection]
  change (rawProjection k G n).hom ((basisIso k G n).hom.hom (standardSymbol k G n a r)) = 0
  rw [basisIso_hom_single, rawProjection_single_single]
  have hdeg : ¬ IsNondegenerate G (fun j => (a j.castSucc)⁻¹ * a j.succ) := by
    intro h
    exact h i (by simp [ha])
  rw [dite_eq_right hdeg]

/-- A native simplicial degeneracy repeats its indexed entry. -/
theorem standard_sigma_single (n : ℕ) (i : Fin (n + 1)) (a : Fin (n + 1) → G) (r : k) :
    ((standardSimplicial k G).σ i).hom (standardSymbol k G n a r) =
      standardSymbol k G (n + 1) (a ∘ i.predAbove) r := by
  let σn : k[Fin (n + 1) → G] →ₗ[k] k[Fin (n + 2) → G] :=
    ((standardSimplicial k G).σ i).hom.toLinearMap
  have hσ : σn = MonoidAlgebra.mapDomainLinearMap k k
      (fun b : Fin (n + 1) → G => b ∘ i.predAbove) := rfl
  change σn (MonoidAlgebra.single a r) = MonoidAlgebra.single (a ∘ i.predAbove) r
  rw [hσ]
  exact MonoidAlgebra.mapDomainLinearMap_single (R := k) (S := k)
    (fun b : Fin (n + 1) → G => b ∘ i.predAbove) r a

/-- Tuple projection vanishes on every actual simplicial degeneracy. -/
theorem standardProjection_degeneraciesVanish (n : ℕ) :
    AlgebraicTopology.DoldKan.DegeneraciesVanish
      (X := standardSimplicial k G) (standardProjection k G n) := by
  cases n with
  | zero =>
    exact (AlgebraicTopology.DoldKan.degeneraciesVanish_zero_iff_true
      (X := standardSimplicial k G) (standardProjection k G 0)).mpr True.intro
  | succ n =>
    refine (AlgebraicTopology.DoldKan.degeneraciesVanish_succ_iff
      (X := standardSimplicial k G) (standardProjection k G (n + 1))).mpr ?_
    intro i
    let σn : k[Fin (n + 1) → G] →ₗ[k] k[Fin (n + 2) → G] :=
      ((standardSimplicial k G).σ i).hom.toLinearMap
    let πn : k[Fin (n + 2) → G] →ₗ[k] (Tuple G (n + 1) →₀ k[G]) :=
      (standardProjection k G (n + 1)).hom.toLinearMap
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    change πn.comp σn = 0
    refine MonoidAlgebra.lhom_ext' (fun a => LinearMap.ext_ring ?_)
    change πn (σn (MonoidAlgebra.single a (1 : k))) = 0
    have hσ : σn (MonoidAlgebra.single a (1 : k)) =
        MonoidAlgebra.single (a ∘ i.predAbove) (1 : k) :=
      standard_sigma_single k G n i a (1 : k)
    have hπ : πn (MonoidAlgebra.single (a ∘ i.predAbove) (1 : k)) = 0 :=
      standardProjection_single_of_degenerate k G (n + 1) (a ∘ i.predAbove) i
        (by simp only [Function.comp_apply, Fin.predAbove_castSucc_self,
          Fin.predAbove_succ_self]) (1 : k)
    exact (congrArg (fun x : k[Fin (n + 2) → G] => πn x) hσ).trans hπ

/-- Native projector normalization leaves the literal tuple projection unchanged. -/
@[reassoc (attr := simp)]
theorem projector_f_comp_standardProjection (n : ℕ) :
    (projector k G).f n ≫ standardProjection k G n = standardProjection k G n := by
  have hQ := (AlgebraicTopology.DoldKan.degeneraciesVanish_iff_QInfty_f_comp
    (standardProjection k G n)).mp (standardProjection_degeneraciesVanish k G n)
  have h := congrArg (fun f => f ≫ standardProjection k G n)
    (AlgebraicTopology.DoldKan.PInfty_f_add_QInfty_f (X := standardSimplicial k G) n)
  simpa only [Preadditive.add_comp, hQ, add_zero, Category.id_comp] using h

/-- Every homogeneous simplex with repeated adjacent entries is killed by
the actual native normalization projector. -/
theorem projector_single_of_degenerate (n : ℕ) (a : Fin (n + 1) → G)
    (i : Fin n) (ha : a i.castSucc = a i.succ) (r : k) :
    ((projector k G).f n).hom (standardSymbol k G n a r) = 0 := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    let b : Fin (n + 1) → G := a ∘ i.castSucc.succAbove
    have heq : a = b ∘ i.predAbove := by
      funext j
      by_cases hj : j = i.castSucc
      · subst j
        simpa only [b, Function.comp_apply, Fin.predAbove_castSucc_self,
          Fin.succAbove_castSucc_self] using ha
      · simp only [b, Function.comp_apply, Fin.succAbove_predAbove hj]
    have h := congrArg
      (fun f : (standardSimplicial k G).obj (Opposite.op ⦋n⦌) ⟶
          (standardSimplicial k G).obj (Opposite.op ⦋n + 1⦌) =>
        f.hom (standardSymbol k G n b r))
      (AlgebraicTopology.DoldKan.σ_comp_PInfty (standardSimplicial k G) i)
    change ((projector k G).f (n + 1)).hom
      (((standardSimplicial k G).σ i).hom (standardSymbol k G n b r)) = 0 at h
    rw [standard_sigma_single] at h
    rw [heq]
    exact h

/-- The raw tuple splitting preserves the normalization projector. This
uses the actual degeneracy of every tuple containing an identity entry. -/
@[reassoc]
theorem standardProjection_comp_rawInclusion_comp_projector (n : ℕ) :
    standardProjection k G n ≫ standardRawInclusion k G n ≫ (projector k G).f n =
      (projector k G).f n := by
  classical
  apply (cancel_epi (basisIso k G n).inv).mp
  simp only [standardProjection, standardRawInclusion, Category.assoc, Iso.inv_hom_id_assoc]
  refine Rep.free_ext k G _ _ _ ?_
  intro g
  let πn : ((Fin n → G) →₀ k[G]) →ₗ[k] (Tuple G n →₀ k[G]) :=
    (rawProjection k G n).hom.toLinearMap
  let ιn : (Tuple G n →₀ k[G]) →ₗ[k] ((Fin n → G) →₀ k[G]) :=
    (rawInclusion k G n).hom.toLinearMap
  let bn : ((Fin n → G) →₀ k[G]) →ₗ[k] k[Fin (n + 1) → G] :=
    (basisIso k G n).inv.hom.toLinearMap
  let pn : k[Fin (n + 1) → G] →ₗ[k] k[Fin (n + 1) → G] :=
    ((projector k G).f n).hom.toLinearMap
  let z : (Fin n → G) →₀ k[G] :=
    Finsupp.single g (MonoidAlgebra.single (1 : G) (1 : k))
  change pn (bn (ιn (πn z))) = pn (bn z)
  have hπ : πn z =
      if hg : IsNondegenerate G g then
        Finsupp.single ⟨g, hg⟩ (MonoidAlgebra.single (1 : G) (1 : k)) else 0 :=
    rawProjection_single_single k G n g (1 : G) (1 : k)
  by_cases hg : IsNondegenerate G g
  · have hπpos : πn z =
        Finsupp.single ⟨g, hg⟩ (MonoidAlgebra.single (1 : G) (1 : k)) :=
      hπ.trans (dite_eq_left hg)
    have hι : ιn (Finsupp.single ⟨g, hg⟩
        (MonoidAlgebra.single (1 : G) (1 : k))) = z :=
      rawInclusion_single_single k G n ⟨g, hg⟩ (1 : G) (1 : k)
    have hιπ : ιn (πn z) = z := (congrArg ιn hπpos).trans hι
    exact congrArg (fun x : (Fin n → G) →₀ k[G] => pn (bn x)) hιπ
  · have hπneg : πn z = 0 := hπ.trans (dite_eq_right hg)
    have hleft : pn (bn (ιn (πn z))) = 0 := by
      rw [hπneg, map_zero, map_zero, map_zero]
    have hb : bn z = standardSymbol k G n ((1 : G) • Fin.partialProd g) (1 : k) :=
      basisIso_inv_single_single k G n g (1 : G) (1 : k)
    obtain ⟨i, hi⟩ : ∃ i, g i = 1 := by
      simpa only [IsNondegenerate, not_forall, not_not] using hg
    have ha : ((1 : G) • Fin.partialProd g) i.castSucc =
        ((1 : G) • Fin.partialProd g) i.succ := by
      simp only [one_smul]
      rw [Fin.partialProd_succ, hi, mul_one]
    have hdeg : pn (standardSymbol k G n ((1 : G) • Fin.partialProd g) (1 : k)) = 0 :=
      projector_single_of_degenerate k G n ((1 : G) • Fin.partialProd g) i ha (1 : k)
    have hright : pn (bn z) = 0 :=
      (congrArg (fun x : k[Fin (n + 1) → G] => pn x) hb).trans hdeg
    exact hleft.trans hright.symm

/-- The literal tuple projection restricted to the actual Moore degree. -/
def toTupleDegree (n : ℕ) : (mooreComplex k G).X n ⟶ degree k G n :=
  (includeMoore k G).f n ≫ standardProjection k G n

/-- A raw nonidentity tuple mapped through the actual normalization projection. -/
def fromTupleDegree (n : ℕ) : degree k G n ⟶ (mooreComplex k G).X n :=
  standardRawInclusion k G n ≫ (normalize k G).f n

@[reassoc (attr := simp)]
theorem fromTupleDegree_comp_toTupleDegree (n : ℕ) :
    fromTupleDegree k G n ≫ toTupleDegree k G n = 𝟙 (degree k G n) := by
  change (standardRawInclusion k G n ≫ (normalize k G).f n) ≫
      ((includeMoore k G).f n ≫ standardProjection k G n) = 𝟙 (degree k G n)
  calc
    (standardRawInclusion k G n ≫ (normalize k G).f n) ≫
        ((includeMoore k G).f n ≫ standardProjection k G n) =
      standardRawInclusion k G n ≫
        ((normalize k G).f n ≫ (includeMoore k G).f n) ≫ standardProjection k G n := by
      simp only [Category.assoc]
    _ = standardRawInclusion k G n ≫ (projector k G).f n ≫ standardProjection k G n := by
      rw [normalize_f_comp_includeMoore_f]
    _ = standardRawInclusion k G n ≫ standardProjection k G n := by
      rw [projector_f_comp_standardProjection]
    _ = 𝟙 (degree k G n) := standardRawInclusion_comp_standardProjection k G n

@[reassoc (attr := simp)]
theorem toTupleDegree_comp_fromTupleDegree (n : ℕ) :
    toTupleDegree k G n ≫ fromTupleDegree k G n = 𝟙 ((mooreComplex k G).X n) := by
  have h : toTupleDegree k G n ≫ fromTupleDegree k G n ≫ (includeMoore k G).f n =
      (includeMoore k G).f n := by
    simp only [toTupleDegree, fromTupleDegree, Category.assoc, normalize_f_comp_includeMoore_f]
    rw [standardProjection_comp_rawInclusion_comp_projector, includeMoore_f_comp_projector_f]
  have h' : (toTupleDegree k G n ≫ fromTupleDegree k G n) ≫ (includeMoore k G).f n =
      (includeMoore k G).f n :=
    (Category.assoc (toTupleDegree k G n) (fromTupleDegree k G n)
      ((includeMoore k G).f n)).trans h
  calc
    toTupleDegree k G n ≫ fromTupleDegree k G n =
        (toTupleDegree k G n ≫ fromTupleDegree k G n) ≫
          ((includeMoore k G).f n ≫ (normalize k G).f n) := by
      rw [includeMoore_f_comp_normalize_f, Category.comp_id]
    _ = ((toTupleDegree k G n ≫ fromTupleDegree k G n) ≫ (includeMoore k G).f n) ≫
        (normalize k G).f n := (Category.assoc _ _ _).symm
    _ = (includeMoore k G).f n ≫ (normalize k G).f n :=
      congrArg (fun f : (mooreComplex k G).X n ⟶ (standardComplex k G).X n =>
        f ≫ (normalize k G).f n) h'
    _ = 𝟙 _ := includeMoore_f_comp_normalize_f k G n

/-- The actual inverse degree maps identify Moore normalization with the
literal free group-ring module on nonidentity tuples. -/
def degreeIso (n : ℕ) : (mooreComplex k G).X n ≅ degree k G n where
  hom := toTupleDegree k G n
  inv := fromTupleDegree k G n
  hom_inv_id := toTupleDegree_comp_fromTupleDegree k G n
  inv_hom_id := fromTupleDegree_comp_toTupleDegree k G n

/-- The literal normalized group bar complex. Its actual degree objects
are free on nonidentity tuples; the differential is transported from
native normalization through the proved inverse degree maps. -/
def complex : ChainComplex (Rep.{max u v} k G) ℕ :=
  ChainComplex.of (degree k G)
    (fun n => (degreeIso k G (n + 1)).inv ≫ (mooreComplex k G).d (n + 1) n ≫
      (degreeIso k G n).hom) (fun n => by simp [Category.assoc])

/-- The normalization comparison is assembled from the actual degree maps. -/
def mooreIso : mooreComplex k G ≅ complex k G :=
  HomologicalComplex.Hom.isoOfComponents (degreeIso k G) (fun i j hij => by
    obtain rfl : i = j + 1 := hij.symm
    simp [complex])

/-- The canonical quotient projection from the standard group complex. -/
def projection : standardComplex k G ⟶ complex k G :=
  normalize k G ≫ (mooreIso k G).hom

/-- The canonical chain inclusion, corrected by native normalization. -/
def inclusion : complex k G ⟶ standardComplex k G :=
  (mooreIso k G).inv ≫ includeMoore k G

@[reassoc (attr := simp)]
theorem inclusion_comp_projection :
    inclusion k G ≫ projection k G = 𝟙 (complex k G) := by
  simp [inclusion, projection, Category.assoc]

@[reassoc (attr := simp)]
theorem projection_comp_inclusion :
    projection k G ≫ inclusion k G = projector k G := by
  simp [inclusion, projection, Category.assoc]

@[simp]
theorem projection_f (n : ℕ) : (projection k G).f n = standardProjection k G n := by
  have hE : (mooreIso k G).hom.f n = toTupleDegree k G n := rfl
  change (normalize k G).f n ≫ (mooreIso k G).hom.f n = standardProjection k G n
  rw [hE]
  change (normalize k G).f n ≫
    ((includeMoore k G).f n ≫ standardProjection k G n) = standardProjection k G n
  calc
    (normalize k G).f n ≫ ((includeMoore k G).f n ≫ standardProjection k G n) =
        ((normalize k G).f n ≫ (includeMoore k G).f n) ≫ standardProjection k G n :=
      (Category.assoc _ _ _).symm
    _ = (projector k G).f n ≫ standardProjection k G n :=
      congrArg (fun f : (standardComplex k G).X n ⟶ (standardComplex k G).X n =>
        f ≫ standardProjection k G n) (normalize_f_comp_includeMoore_f k G n)
    _ = standardProjection k G n := projector_f_comp_standardProjection k G n

@[simp]
theorem inclusion_f (n : ℕ) :
    (inclusion k G).f n = standardRawInclusion k G n ≫ (projector k G).f n := by
  have hE : (mooreIso k G).inv.f n = fromTupleDegree k G n := rfl
  change (mooreIso k G).inv.f n ≫ (includeMoore k G).f n =
    standardRawInclusion k G n ≫ (projector k G).f n
  rw [hE]
  change (standardRawInclusion k G n ≫ (normalize k G).f n) ≫
    (includeMoore k G).f n = standardRawInclusion k G n ≫ (projector k G).f n
  calc
    (standardRawInclusion k G n ≫ (normalize k G).f n) ≫ (includeMoore k G).f n =
        standardRawInclusion k G n ≫ ((normalize k G).f n ≫ (includeMoore k G).f n) :=
      Category.assoc _ _ _
    _ = standardRawInclusion k G n ≫ (projector k G).f n :=
      congrArg (fun f : (standardComplex k G).X n ⟶ (standardComplex k G).X n =>
        standardRawInclusion k G n ≫ f) (normalize_f_comp_includeMoore_f k G n)

/-- The actual literal normalized complex is homotopy equivalent to the
standard complex, using the native normalization homotopy equivalence. -/
def homotopyEquivStandard : HomotopyEquiv (complex k G) (standardComplex k G) :=
  (HomotopyEquiv.ofIso (mooreIso k G).symm).trans
    AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex

end Rep.NormalizedBar

end
