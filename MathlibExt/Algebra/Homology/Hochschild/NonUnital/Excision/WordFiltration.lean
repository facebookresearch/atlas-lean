/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.Kernels
public import MathlibExt.Algebra.Algebra.NonUnitalIdeal.KSplit
public meta import Lean.Elab.Tactic.Omega

/-!
# Ideal-entry count filtrations and relative word layers

For a tensor word a of length N, count the positions whose entries belong to I. The submodule
S_(N,r) is spanned by pure words with at least r ideal entries; increasing r shrinks this
span. Multiplying adjacent entries loses at most one ideal entry because I is two-sided.

In degree n of the relative naive kernel, pull back S_(n+1,n+1−p) along the word inclusion to
define F_p. Thus F_p is increasing in p. Its predecessor is zero at p = 0 and F_(p−1)
otherwise, and the associated layer is the quotient by that predecessor inside F_p.

With an arbitrary ground coefficient V, the same count ignores V and defines the stage in
positive bar degree n + 1. A ground-linear quotient splitting also gives typed words: false
positions lie in I, true positions lie in the section image, and the true-position count is
the quotient-position count.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex
open scoped TensorProduct NonUnitalSubalgebra.Quotient

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

open ModuleCat.Algebra.Hochschild

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (I : NonUnitalSubalgebra k A) [I.IsTwoSided]

/-- Let k be commutative, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. For a : Fin n → A, idealEntryCount k A I a is the number of i : Fin n with a_i ∈
I.toSubmodule. -/
def idealEntryCount {n : ℕ} (a : Fin n → A) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => a i ∈ I.toSubmodule)).card

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- Let k be commutative, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Assume I is two-sided. For a : Fin (n + 1) → A and i : Fin n, idealEntryCount a
− 1 ≤ idealEntryCount (hochschildMulAdjacent i a), with natural-number subtraction.
Two-sidedness keeps the product in I whenever either multiplied entry is in I. -/
theorem idealEntryCount_mulAdjacent {n : ℕ} (i : Fin n) (a : Fin (n + 1) → A) :
    idealEntryCount k A I a - 1 ≤ idealEntryCount k A I (hochschildMulAdjacent i a) := by
  classical
  let S : Finset (Fin (n + 1)) := Finset.univ.filter (fun j => a j ∈ I.toSubmodule)
  let T : Finset (Fin n) :=
    Finset.univ.filter (fun j => hochschildMulAdjacent i a j ∈ I.toSubmodule)
  have hRestore (j : Fin (n + 1)) (hj : j ≠ i.succ) :
      i.succ.succAbove (i.predAbove j) = j :=
    Fin.succ_succAbove_predAbove hj
  have hMap : Set.MapsTo i.predAbove (S.erase i.succ) T := by
    intro j hj
    rcases Finset.mem_erase.mp hj with ⟨hne, hmem⟩
    have hjI : a j ∈ I.toSubmodule := (Finset.mem_filter.mp hmem).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    by_cases hji : i.predAbove j = i
    · have hleft : i.castSucc = j := by
        simpa only [hji, Fin.succAbove_succ_self] using hRestore j hne
      rw [hochschildMulAdjacent, if_pos hji]
      apply (NonUnitalSubalgebra.mem_toSubmodule I).mpr
      exact NonUnitalSubalgebra.IsTwoSided.mul_mem_right
        ((NonUnitalSubalgebra.mem_toSubmodule I).mp
          (by simpa only [hleft] using hjI)) _
    · rw [hochschildMulAdjacent, if_neg hji, hRestore j hne]
      exact hjI
  have hInj : Set.InjOn i.predAbove (S.erase i.succ) := by
    intro j hj l hl hjl
    have h := congrArg (fun r : Fin n => i.succ.succAbove r) hjl
    exact (hRestore j (Finset.mem_erase.mp hj).1).symm.trans
      (h.trans (hRestore l (Finset.mem_erase.mp hl).1))
  change S.card - 1 ≤ T.card
  exact (Finset.pred_card_le_card_erase (s := S) (a := i.succ)).trans
    (Finset.card_le_card_of_injOn i.predAbove hMap hInj)

/-- Let k be commutative, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. For n, r : ℕ, idealWordSpan k A I n r is the k-submodule of A^⊗n spanned by
tprod a for tuples a : Fin n → A satisfying r ≤ idealEntryCount a. -/
def idealWordSpan (n required : ℕ) : Submodule k (TensorPower k n A) :=
  Submodule.span k {x | ∃ a : Fin n → A,
    required ≤ idealEntryCount k A I a ∧ x = PiTensorProduct.tprod k a}

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be commutative, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. For n : ℕ and s ≤ r, idealWordSpan k A I n r ≤ idealWordSpan k A I n s. -/
theorem idealWordSpan_antitone (n : ℕ) {r s : ℕ} (h : s ≤ r) :
    idealWordSpan k A I n r ≤ idealWordSpan k A I n s := by
  apply Submodule.span_mono
  rintro x ⟨a, ha, rfl⟩
  exact ⟨a, h.trans ha, rfl⟩

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and k-bilinear
multiplication, and I a two-sided nonunital k-subalgebra. Put Q = A/I. Write K_b =
ker(bComplex(A) → bComplex(Q)), and identify its degree-n inclusion with an injective word map
W_n : (K_b)_n → A^⊗(n+1). relativeNaiveWordMap n is TensorPower.consEquiv after the degree-n
kernel inclusion, giving W_n : (K_b)_n →ₗ[k] TensorPower k (n + 1) A. -/
def relativeNaiveWordMap (n : ℕ) :
    (relativeNaiveComplex k A I).X n →ₗ[k] TensorPower k (n + 1) A :=
  (TensorPower.consEquiv k A n).toLinearMap.comp
    ((kernel.ι (cyclicBComplexHom I.quotientMap)).f n).hom

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and k-bilinear
multiplication, and I a two-sided nonunital k-subalgebra. Put Q = A/I. Write K_b =
ker(bComplex(A) → bComplex(Q)), and identify its degree-n inclusion with an injective word map
W_n : (K_b)_n → A^⊗(n+1). For p,n : ℕ, naiveWordFiltration p n is W_n⁻¹(idealWordSpan (n + 1)
(n + 1 − p)). The count uses natural-number subtraction. -/
def naiveWordFiltration (p n : ℕ) : Submodule k ((relativeNaiveComplex k A I).X n) :=
  (idealWordSpan k A I (n + 1) (n + 1 - p)).comap (relativeNaiveWordMap k A I n)

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and k-bilinear
multiplication, and I a two-sided nonunital k-subalgebra. Put Q = A/I. Write K_b =
ker(bComplex(A) → bComplex(Q)), and identify its degree-n inclusion with an injective word map
W_n : (K_b)_n → A^⊗(n+1). For p ≤ q and n : ℕ, naiveWordFiltration p n ≤ naiveWordFiltration q
n. Increasing p lowers the required ideal-entry count. -/
theorem naiveWordFiltration_mono {p q : ℕ} (h : p ≤ q) (n : ℕ) :
    naiveWordFiltration k A I p n ≤ naiveWordFiltration k A I q n := by
  apply Submodule.comap_mono
  apply idealWordSpan_antitone
  omega

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and k-bilinear
multiplication, and I a two-sided nonunital k-subalgebra. Put Q = A/I. Write K_b =
ker(bComplex(A) → bComplex(Q)), and identify its degree-n inclusion with an injective word map
W_n : (K_b)_n → A^⊗(n+1). naiveLowerFiltration p n is ⊥ when p = 0 and naiveWordFiltration (p
− 1) n otherwise. -/
def naiveLowerFiltration (p n : ℕ) : Submodule k ((relativeNaiveComplex k A I).X n) :=
  if p = 0 then ⊥ else naiveWordFiltration k A I (p - 1) n

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and k-bilinear
multiplication, and I a two-sided nonunital k-subalgebra. Put Q = A/I. Write K_b =
ker(bComplex(A) → bComplex(Q)), and identify its degree-n inclusion with an injective word map
W_n : (K_b)_n → A^⊗(n+1). naiveWordLayer p n is F_p ⧸ (F_lower.comap F_p.subtype), where F_p =
naiveWordFiltration p n and F_lower = naiveLowerFiltration p n. -/
abbrev naiveWordLayer (p n : ℕ) :=
  naiveWordFiltration k A I p n ⧸
    (naiveLowerFiltration k A I p n).comap (naiveWordFiltration k A I p n).subtype

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and k-bilinear
multiplication, and I a two-sided nonunital k-subalgebra. Put Q = A/I. Write K_b =
ker(bComplex(A) → bComplex(Q)), and identify its degree-n inclusion with an injective word map
W_n : (K_b)_n → A^⊗(n+1). naiveWordLayerProjection p n is the quotient map F_p →ₗ[k]
naiveWordLayer p n by the inverse image of the predecessor under F_p's inclusion. -/
def naiveWordLayerProjection (p n : ℕ) :
    naiveWordFiltration k A I p n →ₗ[k] naiveWordLayer k A I p n :=
  ((naiveLowerFiltration k A I p n).comap (naiveWordFiltration k A I p n).subtype).mkQ

variable (V : Type w) [AddCommGroup V] [Module k V]

/-- Let k be commutative, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let V be a k-module. coefficientIdealWordSpan n r is the span in V ⊗[k] A^⊗n of
v ⊗ tprod a with at least r entries of a in I. The coefficient v is unrestricted. -/
def coefficientIdealWordSpan (n required : ℕ) : Submodule k (V ⊗[k] TensorPower k n A) :=
  Submodule.span k {x | ∃ v : V, ∃ a : Fin n → A,
    required ≤ idealEntryCount k A I a ∧ x = v ⊗ₜ[k] PiTensorProduct.tprod k a}

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
theorem coefficientIdealWordSpan_antitone (n : ℕ) {r s : ℕ} (h : s ≤ r) :
    coefficientIdealWordSpan k A I V n r ≤ coefficientIdealWordSpan k A I V n s := by
  apply Submodule.span_mono
  rintro x ⟨v, a, ha, rfl⟩
  exact ⟨v, a, h.trans ha, rfl⟩

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and k-bilinear
multiplication, and I a two-sided nonunital k-subalgebra. Put Q = A/I. Let V be an arbitrary
k-module in a separate carrier universe. Write K_+ = ker(positiveBar(A,V) → positiveBar(Q,V));
degree n + 1 maps into V ⊗[k] A^⊗(n+1) through W^V_n. For p,n : ℕ, barWordFiltration p n is
(W^V_n)⁻¹(coefficientIdealWordSpan (n + 1) (n + 1 − p)), a submodule of positive degree n + 1. -/
def barWordFiltration (p n : ℕ) :
    Submodule k ((relativePositiveBarComplex k A I V).X (n + 1)) :=
  (coefficientIdealWordSpan k A I V (n + 1) (n + 1 - p)).comap
    (relativePositiveBarWordMap k A I V n)

theorem barWordFiltration_mono {p q : ℕ} (h : p ≤ q) (n : ℕ) :
    barWordFiltration k A I V p n ≤ barWordFiltration k A I V q n := by
  apply Submodule.comap_mono
  apply coefficientIdealWordSpan_antitone
  omega

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and k-bilinear
multiplication, and I a two-sided nonunital k-subalgebra. Put Q = A/I. Let V be an arbitrary
k-module in a separate carrier universe. Write K_+ = ker(positiveBar(A,V) → positiveBar(Q,V));
degree n + 1 maps into V ⊗[k] A^⊗(n+1) through W^V_n. barLowerFiltration p n is ⊥ at p = 0 and
barWordFiltration (p − 1) n otherwise. -/
def barLowerFiltration (p n : ℕ) :
    Submodule k ((relativePositiveBarComplex k A I V).X (n + 1)) :=
  if p = 0 then ⊥ else barWordFiltration k A I V (p - 1) n

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and k-bilinear
multiplication, and I a two-sided nonunital k-subalgebra. Put Q = A/I. Let V be an arbitrary
k-module in a separate carrier universe. Write K_+ = ker(positiveBar(A,V) → positiveBar(Q,V));
degree n + 1 maps into V ⊗[k] A^⊗(n+1) through W^V_n. barWordLayer p n is barWordFiltration p
n modulo the inverse image of barLowerFiltration p n inside that current stage. -/
abbrev barWordLayer (p n : ℕ) :=
  barWordFiltration k A I V p n ⧸
    (barLowerFiltration k A I V p n).comap (barWordFiltration k A I V p n).subtype

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and k-bilinear
multiplication, and I a two-sided nonunital k-subalgebra. Put Q = A/I. Let V be an arbitrary
k-module in a separate carrier universe. Write K_+ = ker(positiveBar(A,V) → positiveBar(Q,V));
degree n + 1 maps into V ⊗[k] A^⊗(n+1) through W^V_n. barWordLayerProjection p n is the
k-linear quotient map from barWordFiltration p n to barWordLayer p n. -/
def barWordLayerProjection (p n : ℕ) :
    barWordFiltration k A I V p n →ₗ[k] barWordLayer k A I V p n :=
  ((barLowerFiltration k A I V p n).comap (barWordFiltration k A I V p n).subtype).mkQ

section SplitWordCoordinates

variable (splitting : I.KSplit)

/-- Let k be commutative, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let s : I.KSplit be a k-linear section of A → A/I. For colour : Fin n → Bool and
a : Fin n → A, splitWordTyped means a_i belongs to the range of s.sectionMap when colour i is
true, and to I.toSubmodule when colour i is false. -/
def splitWordTyped {n : ℕ} (color : Fin n → Bool) (a : Fin n → A) : Prop :=
  ∀ i, if color i then a i ∈ splitting.sectionMap.range else a i ∈ I.toSubmodule

/-- For a colour function colour : Fin n → Bool, quotientEntryCount colour is the number of i :
Fin n with colour i = true. In split-word typing these are the quotient-section positions. -/
def quotientEntryCount {n : ℕ} (color : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => color i = true)).card

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and k-bilinear
multiplication, and I a two-sided nonunital k-subalgebra. Put Q = A/I. Write K_b =
ker(bComplex(A) → bComplex(Q)), and identify its degree-n inclusion with an injective word map
W_n : (K_b)_n → A^⊗(n+1). For a submodule S ≤ A^⊗(n+1), naiveLayerImage p n S is obtained by
pulling S back along W_n, restricting to naiveWordFiltration p n, then taking its image under
naiveWordLayerProjection p n. -/
def naiveLayerImage (p n : ℕ) (S : Submodule k (TensorPower k (n + 1) A)) :
    Submodule k (naiveWordLayer k A I p n) :=
  ((S.comap (relativeNaiveWordMap k A I n)).comap
    (naiveWordFiltration k A I p n).subtype).map (naiveWordLayerProjection k A I p n)

end SplitWordCoordinates

end ModuleCat.Algebra.Hochschild.NonUnital
