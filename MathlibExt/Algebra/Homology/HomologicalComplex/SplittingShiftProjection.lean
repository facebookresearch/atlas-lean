/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.SplittingShift
public import MathlibExt.Algebra.Homology.HomologicalComplex.SplittingProjection
public import MathlibExt.Algebra.Homology.CochainComplex.Splitting

/-!
# Native signed shift of normalized degree projectors

The native sign appears once in the differential and once in its inverse.
It cancels in both degree projectors, so the complementary projector shifts
without a sign. All APIs in this module use preadditivity and actual integer
chain/cochain shifts, with no homology or abelian-category premise.
-/

@[expose] public section

open CategoryTheory HomologicalComplex

namespace HomologicalComplex.Splitting

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]

section Cochain

variable {K : CochainComplex C ℤ}

/-- The native cochain outgoing projector keeps its translated components with no sign. -/
lemma cochainShift_dNext (s : Splitting K) (a i : ℤ) :
    dNext i (s.cochainShift a).hom = dNext (i + a) s.hom := by
  have hnext (p : ℤ) : (ComplexShape.up ℤ).next p = p + 1 :=
    (ComplexShape.up ℤ).next_eq' (by rfl)
  have ht : (ComplexShape.up ℤ).next i + a = (ComplexShape.up ℤ).next (i + a) := by
    rw [hnext, hnext]
    omega
  change (a.negOnePow • K.d (i + a) ((ComplexShape.up ℤ).next i + a)) ≫
      (a.negOnePow • s.hom ((ComplexShape.up ℤ).next i + a) (i + a)) =
    K.d (i + a) ((ComplexShape.up ℤ).next (i + a)) ≫
      s.hom ((ComplexShape.up ℤ).next (i + a)) (i + a)
  rw [ht]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
    Int.units_mul_self, one_smul]

/-- The native cochain incoming projector keeps its translated components with no sign. -/
lemma cochainShift_prevD (s : Splitting K) (a i : ℤ) :
    prevD i (s.cochainShift a).hom = prevD (i + a) s.hom := by
  have hprev (p : ℤ) : (ComplexShape.up ℤ).prev p = p - 1 :=
    (ComplexShape.up ℤ).prev_eq' (by change (p - 1) + 1 = p; omega)
  have ht : (ComplexShape.up ℤ).prev i + a = (ComplexShape.up ℤ).prev (i + a) := by
    rw [hprev, hprev]
    omega
  change (a.negOnePow • s.hom (i + a) ((ComplexShape.up ℤ).prev i + a)) ≫
      (a.negOnePow • K.d ((ComplexShape.up ℤ).prev i + a) (i + a)) =
    s.hom (i + a) ((ComplexShape.up ℤ).prev (i + a)) ≫
      K.d ((ComplexShape.up ℤ).prev (i + a)) (i + a)
  rw [ht]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
    Int.units_mul_self, one_smul]

/-- The normalized cochain outgoing projector retains the same translated component. -/
lemma cochainShift_normalize_dNext (s : Splitting K) (a i : ℤ) :
    dNext i (s.cochainShift a).normalize.hom = dNext (i + a) s.normalize.hom := by
  rw [cochainShift_normalize]
  exact s.normalize.cochainShift_dNext a i

/-- The normalized cochain incoming projector retains the same translated component. -/
lemma cochainShift_normalize_prevD (s : Splitting K) (a i : ℤ) :
    prevD i (s.cochainShift a).normalize.hom = prevD (i + a) s.normalize.hom := by
  rw [cochainShift_normalize]
  exact s.normalize.cochainShift_prevD a i

/-- The actual normalized complex projector is mapped by the native sign-free cochain map. -/
lemma normalizedHomologyProjector_cochainShift (s : Splitting K) (a : ℤ) :
    (CategoryTheory.shiftFunctor (CochainComplex C ℤ) a).map s.normalizedHomologyProjector =
      (s.cochainShift a).normalizedHomologyProjector := by
  ext i
  simp only [CochainComplex.shiftFunctor_map_f', normalizedHomologyProjector_f,
    cochainShift_normalize_dNext, cochainShift_normalize_prevD]
  rfl

/-- The shifted deformation homotopy retains the native single sign on inverse components. -/
lemma homotopyIdNormalizedHomologyProjector_cochainShift_hom
    (s : Splitting K) (a i j : ℤ) :
    (s.cochainShift a).homotopyIdNormalizedHomologyProjector.hom i j =
      a.negOnePow • s.homotopyIdNormalizedHomologyProjector.hom (i + a) (j + a) := by
  simp only [homotopyIdNormalizedHomologyProjector_hom,
    cochainShift_normalize, cochainShift_hom]

end Cochain

section Chain

variable {K : ChainComplex C ℤ}

/-- The native chain outgoing projector keeps both negative indices and no residual sign. -/
lemma chainShift_dNext (s : Splitting K) (a i : ℤ) :
    dNext i (s.chainShift a).hom = dNext (-(-i + a)) s.hom := by
  have hnext (p : ℤ) : (ComplexShape.down ℤ).next p = p - 1 :=
    (ComplexShape.down ℤ).next_eq' (by change (p - 1) + 1 = p; omega)
  have ht : -(-((ComplexShape.down ℤ).next i) + a) =
      (ComplexShape.down ℤ).next (-(-i + a)) := by
    rw [hnext, hnext]
    omega
  change (a.negOnePow • K.d (-(-i + a)) (-(-((ComplexShape.down ℤ).next i) + a))) ≫
      (a.negOnePow • s.hom (-(-((ComplexShape.down ℤ).next i) + a)) (-(-i + a))) =
    K.d (-(-i + a)) ((ComplexShape.down ℤ).next (-(-i + a))) ≫
      s.hom ((ComplexShape.down ℤ).next (-(-i + a))) (-(-i + a))
  rw [ht]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
    Int.units_mul_self, one_smul]

/-- The native chain incoming projector keeps both negative indices and no residual sign. -/
lemma chainShift_prevD (s : Splitting K) (a i : ℤ) :
    prevD i (s.chainShift a).hom = prevD (-(-i + a)) s.hom := by
  have hprev (p : ℤ) : (ComplexShape.down ℤ).prev p = p + 1 :=
    (ComplexShape.down ℤ).prev_eq' (by rfl)
  have ht : -(-((ComplexShape.down ℤ).prev i) + a) =
      (ComplexShape.down ℤ).prev (-(-i + a)) := by
    rw [hprev, hprev]
    omega
  change (a.negOnePow • s.hom (-(-i + a)) (-(-((ComplexShape.down ℤ).prev i) + a))) ≫
      (a.negOnePow • K.d (-(-((ComplexShape.down ℤ).prev i) + a)) (-(-i + a))) =
    s.hom (-(-i + a)) ((ComplexShape.down ℤ).prev (-(-i + a))) ≫
      K.d ((ComplexShape.down ℤ).prev (-(-i + a))) (-(-i + a))
  rw [ht]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
    Int.units_mul_self, one_smul]

/-- The normalized native chain outgoing projector retains its actual translated component. -/
lemma chainShift_normalize_dNext (s : Splitting K) (a i : ℤ) :
    dNext i (s.chainShift a).normalize.hom = dNext (-(-i + a)) s.normalize.hom := by
  rw [chainShift_normalize]
  exact s.normalize.chainShift_dNext a i

/-- The normalized native chain incoming projector retains its actual translated component. -/
lemma chainShift_normalize_prevD (s : Splitting K) (a i : ℤ) :
    prevD i (s.chainShift a).normalize.hom = prevD (-(-i + a)) s.normalize.hom := by
  rw [chainShift_normalize]
  exact s.normalize.chainShift_prevD a i

/-- The actual normalized chain projector is mapped by the native shift facade. -/
lemma normalizedHomologyProjector_chainShift (s : Splitting K) (a : ℤ) :
    (ChainComplex.nativeShift C a).map s.normalizedHomologyProjector =
      (s.chainShift a).normalizedHomologyProjector := by
  ext i
  simp only [ChainComplex.nativeShift_map_f, normalizedHomologyProjector_f,
    chainShift_normalize_dNext, chainShift_normalize_prevD]
  rfl

end Chain

end HomologicalComplex.Splitting

namespace CochainComplex

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The literal cochain source family shifts with the native sign and required source equality map. -/
lemma splittingOfDegreeMinusOneHom_shift_hom_succ (K : CochainComplex C ℤ)
    (s : ∀ n : ℤ, K.X (n + 1) ⟶ K.X n)
    (hs : ∀ n : ℤ, K.d n (n + 1) = K.d n (n + 1) ≫ s n ≫ K.d n (n + 1))
    (a n : ℤ) :
    ((splittingOfDegreeMinusOneHom K s hs).cochainShift a).hom (n + 1) n =
      (K.XIsoOfEq (show (n + 1) + a = (n + a) + 1 by omega)).hom ≫
        (a.negOnePow • s (n + a)) := by
  have he : (n + 1) + a = (n + a) + 1 := by omega
  have hh := (splittingOfDegreeMinusOneHom K s hs).hom_XIsoOfEq he (rfl : n + a = n + a)
  rw [splittingOfDegreeMinusOneHom_hom_succ] at hh
  simp only [XIsoOfEq_rfl, Iso.refl_inv, Category.comp_id] at hh
  rw [HomologicalComplex.Splitting.cochainShift_hom, hh, Linear.comp_units_smul]

end CochainComplex
