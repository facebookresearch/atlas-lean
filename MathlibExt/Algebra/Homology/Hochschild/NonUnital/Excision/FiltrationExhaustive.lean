/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.NaiveFiltrationComplex
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.PositiveBarAssociatedGraded

/-!
# Degreewise exhaustion and zero associated layers

Requiring no ideal entries spans the entire ambient tensor power, with or without a passive
coefficient V. Hence in degree n the relative naive filtration is full once p ≥ n + 1, and its
supremum over p is the full kernel term. The stage inclusion is then an isomorphism in that
particular degree. The predecessor is also full when p > n + 1, making the associated layer
zero.

In positive bar degree N, the full stage is exhausted when p ≥ N and the associated quotient
is zero when p > N. Degree zero is a zero ambient object, so its defined bottom stage is also
top. These are degreewise filtration statements.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex
open scoped TensorProduct NonUnitalSubalgebra.Quotient

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (I : NonUnitalSubalgebra k A) [I.IsTwoSided]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- For a nonunital k-module ring A and k-subalgebra I over a commutative k, idealWordSpan n 0 = ⊤
in A^⊗n for every n : ℕ. -/
theorem idealWordSpan_zero (n : ℕ) :
    idealWordSpan k A I n 0 = ⊤ := by
  have hs : {x | ∃ a : Fin n → A,
      0 ≤ idealEntryCount k A I a ∧ x = PiTensorProduct.tprod k a} =
      Set.range (PiTensorProduct.tprod k : (Fin n → A) → TensorPower k n A) := by
    ext x
    constructor
    · rintro ⟨a, _ha, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, Nat.zero_le _, rfl⟩
  rw [idealWordSpan, hs, PiTensorProduct.span_tprod_eq_top]

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let K_b be the relative naive kernel, with degree-n stages
F_p,n requiring n + 1 − p ideal entries. If n + 1 ≤ p, then naiveWordFiltration p n = ⊤ in
K_b.X n. -/
theorem naiveWordFiltration_eq_top {p n : ℕ} (h : n + 1 ≤ p) :
    naiveWordFiltration k A I p n = ⊤ := by
  rw [naiveWordFiltration, Nat.sub_eq_zero_of_le h, idealWordSpan_zero,
    Submodule.comap_top]

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let K_b be the relative naive kernel, with degree-n stages
F_p,n requiring n + 1 − p ideal entries. For every n : ℕ, ⨆ p : ℕ, naiveWordFiltration p n =
⊤. -/
theorem naiveWordFiltration_iSup (n : ℕ) :
    (⨆ p : ℕ, naiveWordFiltration k A I p n) = ⊤ := by
  apply top_unique
  rw [← naiveWordFiltration_eq_top k A I (p := n + 1) (le_refl _)]
  exact le_iSup (fun p : ℕ => naiveWordFiltration k A I p n) (n + 1)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let K_b be the relative naive kernel, with degree-n stages
F_p,n requiring n + 1 − p ideal entries. If n + 1 ≤ p, the underlying map
(naiveFilteredWordInclusion p).f n is bijective. -/
theorem naiveFilteredWordInclusion_f_bijective {p n : ℕ} (h : n + 1 ≤ p) :
    Function.Bijective ((naiveFilteredWordInclusion k A I p).f n).hom := by
  change Function.Bijective (naiveWordFiltration k A I p n).subtype
  refine ⟨Subtype.val_injective, ?_⟩
  intro x
  refine ⟨⟨x, ?_⟩, rfl⟩
  rw [naiveWordFiltration_eq_top k A I h]
  exact Submodule.mem_top

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let K_b be the relative naive kernel, with degree-n stages
F_p,n requiring n + 1 − p ideal entries. If n + 1 ≤ p, IsIso ((naiveFilteredWordInclusion p).f
n) holds in the module category. -/
theorem naiveFilteredWordInclusion_f_isIso {p n : ℕ} (h : n + 1 ≤ p) :
    IsIso ((naiveFilteredWordInclusion k A I p).f n) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (naiveFilteredWordInclusion_f_bijective k A I h)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let K_b be the relative naive kernel, with degree-n stages
F_p,n requiring n + 1 − p ideal entries. If n + 1 < p, naiveLowerFiltration p n = ⊤. Here the
predecessor is F_(p−1),n, since p is positive. -/
theorem naiveLowerFiltration_eq_top {p n : ℕ} (h : n + 1 < p) :
    naiveLowerFiltration k A I p n = ⊤ := by
  have hp : p ≠ 0 := by omega
  have hb : n + 1 ≤ p - 1 := by omega
  rw [naiveLowerFiltration, ite_eq_right hp, naiveWordFiltration_eq_top k A I hb]

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let K_b be the relative naive kernel, with degree-n stages
F_p,n requiring n + 1 − p ideal entries. If n + 1 < p, naiveWordLayer p n is a subsingleton
k-module because both current and predecessor stages are top. -/
theorem naiveWordLayer_subsingleton {p n : ℕ} (h : n + 1 < p) :
    Subsingleton (naiveWordLayer k A I p n) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  rw [naiveLowerFiltration_eq_top k A I h, Submodule.comap_top]

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let K_b be the relative naive kernel, with degree-n stages
F_p,n requiring n + 1 − p ideal entries. If n + 1 < p, (naiveAssociatedWordComplex p).X n is a
zero object. -/
theorem naiveAssociatedWordComplex_isZero {p n : ℕ} (h : n + 1 < p) :
    IsZero ((naiveAssociatedWordComplex k A I p).X n) := by
  change IsZero (ModuleCat.of k (naiveWordLayer k A I p n))
  exact ModuleCat.isZero_iff_subsingleton.mpr (naiveWordLayer_subsingleton k A I h)

variable (V : Type w) [AddCommGroup V] [Module k V]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be commutative, A a nonunital k-module ring, I a k-subalgebra and V a k-module. For
every n : ℕ, coefficientIdealWordSpan V n 0 = ⊤ in V ⊗[k] A^⊗n. -/
theorem coefficientIdealWordSpan_zero (n : ℕ) :
    coefficientIdealWordSpan k A I V n 0 = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul v t =>
      refine PiTensorProduct.induction_on t (fun r a => ?_) (fun x y hx hy => ?_)
      · rw [TensorProduct.tmul_smul]
        apply Submodule.smul_mem
        exact Submodule.subset_span ⟨v, a, Nat.zero_le _, rfl⟩
      · rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ hx hy
  | add x y hx hy => exact Submodule.add_mem _ hx hy

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and V any k-module. Let K_+ be
the relative positive bar kernel. Its full stages G_p,0 are zero and G_p,n+1 =
barWordFiltration p n; a word in degree N > 0 has length N. If n + 1 ≤ p, barWordFiltration p
n = ⊤ in K_+.X (n + 1). -/
theorem barWordFiltration_eq_top {p n : ℕ} (h : n + 1 ≤ p) :
    barWordFiltration k A I V p n = ⊤ := by
  rw [barWordFiltration, Nat.sub_eq_zero_of_le h, coefficientIdealWordSpan_zero,
    Submodule.comap_top]

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and V any k-module. Let K_+ be
the relative positive bar kernel. Its full stages G_p,0 are zero and G_p,n+1 =
barWordFiltration p n; a word in degree N > 0 has length N. For every n : ℕ, ⨆ p : ℕ,
barWordFiltration p n = ⊤ in degree n + 1. -/
theorem barWordFiltration_iSup (n : ℕ) :
    (⨆ p : ℕ, barWordFiltration k A I V p n) = ⊤ := by
  apply top_unique
  rw [← barWordFiltration_eq_top k A I V (p := n + 1) (le_refl _)]
  exact le_iSup (fun p : ℕ => barWordFiltration k A I V p n) (n + 1)

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and V any k-module. Let K_+ be
the relative positive bar kernel. Its full stages G_p,0 are zero and G_p,n+1 =
barWordFiltration p n; a word in degree N > 0 has length N. For every p : ℕ,
barFullWordFiltration p 0 = ⊤. Its definition is ⊥, and the equality holds because K_+.X 0 is
zero. -/
theorem barFullWordFiltration_zero_eq_top (p : ℕ) :
    barFullWordFiltration k A I V p 0 = ⊤ := by
  have : Subsingleton ((relativePositiveBarComplex k A I V).X 0) :=
    ModuleCat.isZero_iff_subsingleton.mp (relativePositiveBarComplex_isZero_zero k A I V)
  apply Submodule.eq_top_iff'.mpr
  intro x
  change x = 0
  exact Subsingleton.elim _ _

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and V any k-module. Let K_+ be
the relative positive bar kernel. Its full stages G_p,0 are zero and G_p,n+1 =
barWordFiltration p n; a word in degree N > 0 has length N. If N ≤ p, barFullWordFiltration p
N = ⊤ for N : ℕ, including the zero ambient degree N = 0. -/
theorem barFullWordFiltration_eq_top {p n : ℕ} (h : n ≤ p) :
    barFullWordFiltration k A I V p n = ⊤ := by
  cases n with
  | zero => exact barFullWordFiltration_zero_eq_top k A I V p
  | succ n => exact barWordFiltration_eq_top k A I V h

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and V any k-module. Let K_+ be
the relative positive bar kernel. Its full stages G_p,0 are zero and G_p,n+1 =
barWordFiltration p n; a word in degree N > 0 has length N. For every N : ℕ, ⨆ p : ℕ,
barFullWordFiltration p N = ⊤. -/
theorem barFullWordFiltration_iSup (n : ℕ) :
    (⨆ p : ℕ, barFullWordFiltration k A I V p n) = ⊤ := by
  apply top_unique
  rw [← barFullWordFiltration_eq_top k A I V (p := n) (le_refl _)]
  exact le_iSup (fun p : ℕ => barFullWordFiltration k A I V p n) n

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and V any k-module. Let K_+ be
the relative positive bar kernel. Its full stages G_p,0 are zero and G_p,n+1 =
barWordFiltration p n; a word in degree N > 0 has length N. If N ≤ p, the underlying map
(barFilteredWordInclusion p).f N is bijective. -/
theorem barFilteredWordInclusion_f_bijective {p n : ℕ} (h : n ≤ p) :
    Function.Bijective ((barFilteredWordInclusion k A I V p).f n).hom := by
  change Function.Bijective (barFullWordFiltration k A I V p n).subtype
  refine ⟨Subtype.val_injective, ?_⟩
  intro x
  refine ⟨⟨x, ?_⟩, rfl⟩
  rw [barFullWordFiltration_eq_top k A I V h]
  exact Submodule.mem_top

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and V any k-module. Let K_+ be
the relative positive bar kernel. Its full stages G_p,0 are zero and G_p,n+1 =
barWordFiltration p n; a word in degree N > 0 has length N. If N ≤ p, IsIso
((barFilteredWordInclusion p).f N) holds. -/
theorem barFilteredWordInclusion_f_isIso {p n : ℕ} (h : n ≤ p) :
    IsIso ((barFilteredWordInclusion k A I V p).f n) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (barFilteredWordInclusion_f_bijective k A I V h)

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and V any k-module. Let K_+ be
the relative positive bar kernel. Its full stages G_p,0 are zero and G_p,n+1 =
barWordFiltration p n; a word in degree N > 0 has length N. If n + 1 < p, barLowerFiltration p
n = ⊤ in positive degree n + 1. -/
theorem barLowerFiltration_eq_top {p n : ℕ} (h : n + 1 < p) :
    barLowerFiltration k A I V p n = ⊤ := by
  have hp : p ≠ 0 := by omega
  have hb : n + 1 ≤ p - 1 := by omega
  rw [barLowerFiltration, ite_eq_right hp, barWordFiltration_eq_top k A I V hb]

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and V any k-module. Let K_+ be
the relative positive bar kernel. Its full stages G_p,0 are zero and G_p,n+1 =
barWordFiltration p n; a word in degree N > 0 has length N. If n + 1 < p, barWordLayer p n is
a subsingleton module. -/
theorem barWordLayer_subsingleton {p n : ℕ} (h : n + 1 < p) :
    Subsingleton (barWordLayer k A I V p n) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  rw [barLowerFiltration_eq_top k A I V h, Submodule.comap_top]

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and V any k-module. Let K_+ be
the relative positive bar kernel. Its full stages G_p,0 are zero and G_p,n+1 =
barWordFiltration p n; a word in degree N > 0 has length N. If N < p,
barFullLowerWordFiltration p N = ⊤. -/
theorem barFullLowerWordFiltration_eq_top {p n : ℕ} (h : n < p) :
    barFullLowerWordFiltration k A I V p n = ⊤ := by
  have hp : p ≠ 0 := by omega
  have hb : n ≤ p - 1 := by omega
  rw [barFullLowerWordFiltration, ite_eq_right hp, barFullWordFiltration_eq_top k A I V hb]

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and V any k-module. Let K_+ be
the relative positive bar kernel. Its full stages G_p,0 are zero and G_p,n+1 =
barWordFiltration p n; a word in degree N > 0 has length N. If N < p, barFullWordLayer p N is
a subsingleton module. -/
theorem barFullWordLayer_subsingleton {p n : ℕ} (h : n < p) :
    Subsingleton (barFullWordLayer k A I V p n) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  rw [barFullLowerWordFiltration_eq_top k A I V h, Submodule.comap_top]

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and V any k-module. Let K_+ be
the relative positive bar kernel. Its full stages G_p,0 are zero and G_p,n+1 =
barWordFiltration p n; a word in degree N > 0 has length N. If N < p,
(barAssociatedWordComplex p).X N is a zero object. -/
theorem barAssociatedWordComplex_isZero {p n : ℕ} (h : n < p) :
    IsZero ((barAssociatedWordComplex k A I V p).X n) := by
  change IsZero (ModuleCat.of k (barFullWordLayer k A I V p n))
  exact ModuleCat.isZero_iff_subsingleton.mpr (barFullWordLayer_subsingleton k A I V h)

end ModuleCat.Algebra.Hochschild.NonUnital
