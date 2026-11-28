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
# Shift signs in normalized projectors and homotopies

The signed shifts of both the differential and splitting inverse cancel
in their degree-zero incoming and outgoing projectors. Thus cochain
projectors translate by i↦i+a and chain projectors by i↦i−a.

The reverse-degree deformation homotopy retains one factor (−1)^a,
as does an adjacent degree-lowering inverse family.
-/

@[expose] public section

open CategoryTheory HomologicalComplex

namespace HomologicalComplex.Splitting

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]

section Cochain

variable {K : CochainComplex C ℤ}

/--
Let K be an integer cochain complex in a preadditive category C, s a splitting and a,i∈ℤ. The
shifted degree i is K^{i+a}, and both its differential and inverse family carry the sign
(−1)^a. The outgoing degree endomorphism has no remaining sign: dNext i(s.cochainShift
a).hom=dNext(i+a)s.hom.
-/
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

/--
Let K be an integer cochain complex in a preadditive category C, s a splitting and a,i∈ℤ. The
shifted degree i is K^{i+a}, and both its differential and inverse family carry the sign
(−1)^a. The incoming degree endomorphism has no remaining sign: prevD i(s.cochainShift
a).hom=prevD(i+a)s.hom.
-/
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

/--
Let K be an integer cochain complex in a preadditive category C, s a splitting and a,i∈ℤ. The
shifted degree i is K^{i+a}, and both its differential and inverse family carry the sign
(−1)^a. For the square-zero normalization n, the outgoing projector satisfies dNext
i(s.cochainShift a).normalize.hom=dNext(i+a)s.normalize.hom.
-/
lemma cochainShift_normalize_dNext (s : Splitting K) (a i : ℤ) :
    dNext i (s.cochainShift a).normalize.hom = dNext (i + a) s.normalize.hom := by
  rw [cochainShift_normalize]
  exact s.normalize.cochainShift_dNext a i

/--
Let K be an integer cochain complex in a preadditive category C, s a splitting and a,i∈ℤ. The
shifted degree i is K^{i+a}, and both its differential and inverse family carry the sign
(−1)^a. For the square-zero normalization n, the incoming projector satisfies prevD
i(s.cochainShift a).normalize.hom=prevD(i+a)s.normalize.hom.
-/
lemma cochainShift_normalize_prevD (s : Splitting K) (a i : ℤ) :
    prevD i (s.cochainShift a).normalize.hom = prevD (i + a) s.normalize.hom := by
  rw [cochainShift_normalize]
  exact s.normalize.cochainShift_prevD a i

/--
Let K be an integer cochain complex in a preadditive category C, s a splitting and a,i∈ℤ. The
shifted degree i is K^{i+a}, and both its differential and inverse family carry the sign
(−1)^a. Shifting the complementary complex endomorphism P_s gives P_{s.cochainShift a}; its
degree-i component is the original projector at i+a.
-/
lemma normalizedHomologyProjector_cochainShift (s : Splitting K) (a : ℤ) :
    (CategoryTheory.shiftFunctor (CochainComplex C ℤ) a).map s.normalizedHomologyProjector =
      (s.cochainShift a).normalizedHomologyProjector := by
  ext i
  simp only [CochainComplex.shiftFunctor_map_f', normalizedHomologyProjector_f,
    cochainShift_normalize_dNext, cochainShift_normalize_prevD]
  rfl

/--
Let K be an integer cochain complex in a preadditive category C, s a splitting and a,i∈ℤ. The
shifted degree i is K^{i+a}, and both its differential and inverse family carry the sign
(−1)^a. If H:1_K∼P_s is the normalized deformation homotopy, its shifted component is
H'_ij=(−1)^a•H_{i+a,j+a}. The degree-zero projector itself remains sign-free.
-/
lemma homotopyIdNormalizedHomologyProjector_cochainShift_hom
    (s : Splitting K) (a i j : ℤ) :
    (s.cochainShift a).homotopyIdNormalizedHomologyProjector.hom i j =
      a.negOnePow • s.homotopyIdNormalizedHomologyProjector.hom (i + a) (j + a) := by
  simp only [homotopyIdNormalizedHomologyProjector_hom,
    cochainShift_normalize, cochainShift_hom]

end Cochain

section Chain

variable {K : ChainComplex C ℤ}

/--
Let K be an integer chain complex in a preadditive category C, s a splitting and a,i∈ℤ. The
chain shift has degree-i term K_{i−a}, with sign (−1)^a on differential and inverse
components. The outgoing projector is dNext i(s.chainShift a).hom=dNext(−(−i+a))s.hom, the
original projector at i−a.
-/
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

/--
Let K be an integer chain complex in a preadditive category C, s a splitting and a,i∈ℤ. The
chain shift has degree-i term K_{i−a}, with sign (−1)^a on differential and inverse
components. The incoming projector is prevD i(s.chainShift a).hom=prevD(−(−i+a))s.hom, with
translated degree i−a and no residual sign.
-/
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

/--
Let K be an integer chain complex in a preadditive category C, s a splitting and a,i∈ℤ. The
chain shift has degree-i term K_{i−a}, with sign (−1)^a on differential and inverse
components. The normalized outgoing projector at shifted degree i equals
dNext(i−a)s.normalize.hom, with i−a represented as −(−i+a).
-/
lemma chainShift_normalize_dNext (s : Splitting K) (a i : ℤ) :
    dNext i (s.chainShift a).normalize.hom = dNext (-(-i + a)) s.normalize.hom := by
  rw [chainShift_normalize]
  exact s.normalize.chainShift_dNext a i

/--
Let K be an integer chain complex in a preadditive category C, s a splitting and a,i∈ℤ. The
chain shift has degree-i term K_{i−a}, with sign (−1)^a on differential and inverse
components. The normalized incoming projector at shifted degree i equals
prevD(i−a)s.normalize.hom, with no remaining shift sign.
-/
lemma chainShift_normalize_prevD (s : Splitting K) (a i : ℤ) :
    prevD i (s.chainShift a).normalize.hom = prevD (-(-i + a)) s.normalize.hom := by
  rw [chainShift_normalize]
  exact s.normalize.chainShift_prevD a i

/--
Let K be an integer chain complex in a preadditive category C, s a splitting and a,i∈ℤ. The
chain shift has degree-i term K_{i−a}, with sign (−1)^a on differential and inverse
components. Applying the chain-shift functor to the normalized complementary endomorphism P_s
gives P_{s.chainShift a}. Its degree components are the original projectors at i−a.
-/
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

/--
Let K be an integer cochain complex in a preadditive category C and let s_n:K^{n+1}→K^n
satisfy d_n≫s_n≫d_n=d_n for every n. Shift the resulting splitting by a∈ℤ. At the adjacent
shifted degrees n+1→n, its component is (−1)^a•s_{n+a}, preceded by the canonical
identification K^{(n+1)+a}≅K^{(n+a)+1}.
-/
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
