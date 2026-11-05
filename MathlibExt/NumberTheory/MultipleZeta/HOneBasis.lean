/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.MultipleZeta.WordAlgebra
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.DFinsupp

/-!
# Hoffman basis of `H^1`

Hoffman monomials indexed by all positive compositions, including the empty
index, form a rational basis of the word subalgebra `hOne` from
`MathlibExt.NumberTheory.MultipleZeta.WordAlgebra`.
-/

@[expose] public section

section
namespace MetaMathlibExt.MultipleZeta

/-- Increment the leading block size; auxiliary for `decodeBlocks`. -/
private def bump : List Nat → List Nat
  | [] => []
  | k :: ks => (k + 1) :: ks

/-- Encode a list of block sizes as a word over `{x, y}`. -/
private def encodeNatBlocks : List Nat → List Bool
  | [] => []
  | k :: ks => List.replicate (k - 1) false ++ [true] ++ encodeNatBlocks ks

/-- Decode a word over `{x, y}` into block sizes, dropping a trailing
open `x`-run (which never occurs for `H^1` words). -/
private def decodeBlocks : List Bool → List Nat
  | [] => []
  | true :: rest => 1 :: decodeBlocks rest
  | false :: rest => bump (decodeBlocks rest)

private theorem bump_ne_nil_of_ne_nil (l : List Nat) (h : l ≠ []) : bump l ≠ [] := by
  cases l with
  | nil => simp at h
  | cons k ks => simp [bump]

private theorem decodeBlocks_pos (l : List Bool) : ∀ x ∈ decodeBlocks l, 0 < x := by
  induction l with
  | nil =>
    intro x hx
    simp [decodeBlocks] at hx
  | cons b rest ih =>
    cases b with
    | true =>
      intro x hx
      simp only [decodeBlocks, List.mem_cons] at hx
      rcases hx with rfl | hx
      · omega
      · exact ih x hx
    | false =>
      intro x hx
      simp only [decodeBlocks] at hx
      cases h : decodeBlocks rest with
      | nil => rw [h] at hx; simp [bump] at hx
      | cons k ks =>
        rw [h] at hx
        simp only [bump, List.mem_cons] at hx
        rcases hx with rfl | hx
        · omega
        · apply ih
          rw [h]
          exact List.mem_cons_of_mem k hx

private theorem decodeBlocks_ne_nil_of_mem_true (l : List Bool) (h : true ∈ l) :
    decodeBlocks l ≠ [] := by
  induction l with
  | nil => simp at h
  | cons b rest ih =>
    cases b with
    | true => simp [decodeBlocks]
    | false =>
      simp only [List.mem_cons, Bool.true_eq_false, false_or]at h
      simp only [decodeBlocks, ne_eq]
      exact bump_ne_nil_of_ne_nil _ (ih h)

private theorem decodeBlocks_append_block (m : Nat) (R : List Bool) :
    decodeBlocks (List.replicate m false ++ [true] ++ R) =
      (m + 1) :: decodeBlocks R := by
  induction m with
  | zero => simp [decodeBlocks]
  | succ n ih =>
    change bump (decodeBlocks (List.replicate n false ++ [true] ++ R)) = _
    rw [ih]
    rfl

private theorem true_mem_of_getLast?_eq_true (rest : List Bool)
    (h : rest.getLast? = some true) : true ∈ rest := by
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp h
  rw [hys]
  exact List.mem_append_right ys (by simp)

private theorem encodeNatBlocks_decodeBlocks (l : List Bool)
    (h : l = [] ∨ l.getLast? = some true) :
    encodeNatBlocks (decodeBlocks l) = l := by
  induction l with
  | nil => simp [decodeBlocks, encodeNatBlocks]
  | cons b rest ih =>
    cases b with
    | true =>
      have hr : rest = [] ∨ rest.getLast? = some true := by
        cases rest with
        | nil => exact Or.inl rfl
        | cons c cs =>
          exact Or.inr (by
            have hlast := Or.resolve_left h (by simp)
            rwa [List.getLast?_cons_cons] at hlast)
      have ihr := ih hr
      simp [decodeBlocks, encodeNatBlocks, ihr]
    | false =>
      cases rest with
      | nil => simp at h
      | cons c cs =>
        have hlast : (c :: cs).getLast? = some true := by
          have hlast := Or.resolve_left h (by simp)
          rwa [List.getLast?_cons_cons] at hlast
        have hr : (c :: cs) = [] ∨ (c :: cs).getLast? = some true :=
          Or.inr hlast
        have ihr := ih hr
        have hmem : true ∈ (c :: cs) := true_mem_of_getLast?_eq_true _ hlast
        have hne : decodeBlocks (c :: cs) ≠ [] :=
          decodeBlocks_ne_nil_of_mem_true _ hmem
        cases hd : decodeBlocks (c :: cs) with
        | nil => exact absurd hd hne
        | cons k ks =>
          have hdec : decodeBlocks (false :: c :: cs) = (k + 1) :: ks := by
            simp [decodeBlocks, hd, bump]
          rw [hdec]
          have henc : encodeNatBlocks ((k + 1) :: ks) =
              List.replicate k false ++ [true] ++ encodeNatBlocks ks := by
            simp [encodeNatBlocks]
          rw [henc]
          have hrest : (c :: cs) = encodeNatBlocks (k :: ks) := by
            rw [← hd]; exact ihr.symm
          have hkpos : 0 < k := decodeBlocks_pos (c :: cs) k (by rw [hd]; simp)
          have hrep : List.replicate k false =
              false :: List.replicate (k - 1) false := by
            cases k with
            | zero => simp at hkpos
            | succ n => simp [List.replicate_succ]
          rw [hrep]
          simp [hrest, encodeNatBlocks]

private theorem pnat_map_val_injective :
    Function.Injective (List.map PNat.val : List PNat → List Nat) := by
  intro l1 l2 h
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons j js => simp at h
  | cons k ks ih =>
    cases l2 with
    | nil => simp at h
    | cons j js =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [Subtype.ext h1, ih h2]

private theorem decode_encode_nat (l : List PNat) :
    decodeBlocks (encodeNatBlocks (l.map PNat.val)) = l.map PNat.val := by
  induction l with
  | nil => simp [encodeNatBlocks, decodeBlocks]
  | cons k ks ih =>
    simp only [List.map_cons, encodeNatBlocks]
    rw [decodeBlocks_append_block, ih]
    have hk : k.val - 1 + 1 = k.val := Nat.sub_add_cancel k.property
    rw [hk]

private theorem index_entries_injective : Function.Injective Index.entries := by
  intro a b h
  rcases a with ⟨n1, c1⟩
  rcases b with ⟨n2, c2⟩
  simp only [Index.entries] at h
  have hn : n1 = n2 := by
    have h1 := c1.blocks_sum
    have h2 := c2.blocks_sum
    rw [← h1, ← h2, h]
  subst hn
  have hc : c1 = c2 := Composition.ext h
  rw [hc]

private theorem pnatEntries_injective : Function.Injective Index.pnatEntries := by
  intro a b h
  have h1 := pnatEntries_val a
  have h2 := pnatEntries_val b
  rw [h] at h1
  have he : a.entries = b.entries := h1.symm.trans h2
  exact index_entries_injective he

private theorem toList_zWordPNat (l : List PNat) :
    FreeMonoid.toList (zWordPNat l) = encodeNatBlocks (l.map PNat.val) := by
  induction l with
  | nil => simp [zWordPNat, encodeNatBlocks]
  | cons k ks ih =>
    have h1 : zWordPNat (k :: ks) = hoffmanBlock k * zWordPNat ks := by
      simp [zWordPNat]
    rw [h1, FreeMonoid.toList_mul, ih]
    simp [encodeNatBlocks, toList_hoffmanBlock]

private theorem zWordPNat_injective : Function.Injective zWordPNat := by
  intro l1 l2 h
  have hlist := congrArg FreeMonoid.toList h
  rw [toList_zWordPNat, toList_zWordPNat] at hlist
  have hdec : decodeBlocks (encodeNatBlocks (l1.map PNat.val)) =
      decodeBlocks (encodeNatBlocks (l2.map PNat.val)) := by rw [hlist]
  rw [decode_encode_nat, decode_encode_nat] at hdec
  exact pnat_map_val_injective hdec

private theorem zWord_injective : Function.Injective zWord := by
  intro a b h
  have hp : a.pnatEntries = b.pnatEntries := zWordPNat_injective h
  exact pnatEntries_injective hp

private theorem mem_HOne_iff_toList (w : FreeMonoid Bool) :
    w ∈ wordSubmonoidHOne ↔
      FreeMonoid.toList w = [] ∨ (FreeMonoid.toList w).getLast? = some true := by
  constructor
  · intro h
    change IsHOneWord w at h
    rcases h with rfl | ⟨u, rfl⟩
    · exact Or.inl FreeMonoid.toList_one
    · right
      have hto : FreeMonoid.toList (u * yWord) =
          FreeMonoid.toList u ++ [true] := by
        rw [FreeMonoid.toList_mul]
        rw [show FreeMonoid.toList yWord = [true] from by simp [yWord]]
      rw [hto]
      exact List.getLast?_eq_some_iff.mpr ⟨_, rfl⟩
  · intro h
    change IsHOneWord w
    rcases h with hnil | hlast
    · left
      have h1 : FreeMonoid.ofList (FreeMonoid.toList w) = w :=
        FreeMonoid.ofList_toList w
      rw [hnil, FreeMonoid.ofList_nil] at h1
      exact h1.symm
    · right
      obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
      refine ⟨FreeMonoid.ofList ys, ?_⟩
      have h1 : FreeMonoid.ofList (FreeMonoid.toList w) = w :=
        FreeMonoid.ofList_toList w
      rw [hys, FreeMonoid.ofList_append] at h1
      have hy : FreeMonoid.ofList [true] = yWord := rfl
      rw [hy] at h1
      exact h1.symm

/-- Index decoding an `H^1` word by splitting after each `y`. -/
private def indexOfHOneWord (w : FreeMonoid Bool) : Index :=
  ⟨(decodeBlocks (FreeMonoid.toList w)).sum,
    ⟨decodeBlocks (FreeMonoid.toList w),
     fun {i} hi => decodeBlocks_pos (FreeMonoid.toList w) i hi, rfl⟩⟩

private theorem zWord_indexOfHOneWord (w : FreeMonoid Bool)
    (h : w ∈ wordSubmonoidHOne) : zWord (indexOfHOneWord w) = w := by
  apply FreeMonoid.toList.injective
  have h1 : FreeMonoid.toList (zWord (indexOfHOneWord w)) =
      encodeNatBlocks ((indexOfHOneWord w).entries) := by
    have h2 := toList_zWordPNat (indexOfHOneWord w).pnatEntries
    rw [pnatEntries_val] at h2
    exact h2
  rw [h1]
  change encodeNatBlocks (decodeBlocks (FreeMonoid.toList w)) = FreeMonoid.toList w
  exact encodeNatBlocks_decodeBlocks _ ((mem_HOne_iff_toList w).mp h)

/-- Linear-equiv version of the free-algebra identification. -/
private noncomputable def freeAlgEquiv :
    FreeAlgebra ℚ Bool ≃ₗ[ℚ] MonoidAlgebra ℚ (FreeMonoid Bool) :=
  (FreeAlgebra.equivMonoidAlgebraFreeMonoid :
    FreeAlgebra ℚ Bool ≃ₐ[ℚ] MonoidAlgebra ℚ (FreeMonoid Bool)).toLinearEquiv

private theorem EL_symm_single (idx : Index) :
    freeAlgEquiv.symm (MonoidAlgebra.single (zWord idx) 1) = zMonomial idx := rfl

private theorem hliM : LinearIndependent ℚ
    (fun w : FreeMonoid Bool => MonoidAlgebra.single w (1 : ℚ)) := by
  have h := (MonoidAlgebra.basis (FreeMonoid Bool) ℚ).linearIndependent
  have h' : (⇑(MonoidAlgebra.basis (FreeMonoid Bool) ℚ)) =
      (fun w : FreeMonoid Bool => MonoidAlgebra.single w (1 : ℚ)) := by
    funext w
    exact MonoidAlgebra.basis_apply ℚ w
  rwa [h'] at h

private theorem hliZ : LinearIndependent ℚ (fun idx : Index => zMonomial idx) := by
  have h := ((MonoidAlgebra.basis (FreeMonoid Bool) ℚ).map
    freeAlgEquiv.symm).linearIndependent.comp (fun idx : Index => zWord idx)
    zWord_injective
  have h2 : (⇑(((MonoidAlgebra.basis (FreeMonoid Bool) ℚ).map
      freeAlgEquiv.symm)) ∘ (fun idx : Index => zWord idx)) =
      (fun idx : Index => zMonomial idx) := by
    funext idx
    simp [Function.comp_apply, Module.Basis.map_apply, MonoidAlgebra.basis_apply,
      EL_symm_single]
  rwa [h2] at h

private theorem hliSub : LinearIndependent ℚ
    (fun idx : Index => (⟨zMonomial idx, zMonomial_mem_hOne idx⟩ : ↥hOne)) :=
  LinearIndependent.of_comp (Submodule.subtype hOne.toSubmodule) hliZ

private theorem hterm_single (w : FreeMonoid Bool) (r : ℚ) :
    Finsupp.single w r = r • Finsupp.single w 1 := by
  simp

private theorem h1_finsupp (f : FreeMonoid Bool →₀ ℚ) :
    f = ∑ w ∈ f.support, f w • Finsupp.single w 1 := by
  conv_lhs => rw [← Finsupp.sum_single f]
  apply Finset.sum_congr rfl
  intro w _
  rw [hterm_single]

private theorem hdecomp (Fx : MonoidAlgebra ℚ (FreeMonoid Bool)) :
    Fx = ∑ w ∈ Fx.coeff.support, Fx.coeff w • MonoidAlgebra.single w (1 : ℚ) := by
  apply MonoidAlgebra.coeff_injective
  rw [MonoidAlgebra.coeff_sum]
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_single]
  exact h1_finsupp Fx.coeff

private theorem hx_span (y : ↥hOne) :
    (↑y : FreeAlgebra ℚ Bool) ∈
      Submodule.span ℚ (Set.range fun idx : Index => zMonomial idx) := by
  set Fx : MonoidAlgebra ℚ (FreeMonoid Bool) :=
    freeAlgEquiv (↑y : FreeAlgebra ℚ Bool) with hFx
  have hsupp : ∀ w ∈ Fx.coeff.support, w ∈ wordSubmonoidHOne := by
    have h := (mem_hOne_iff_support_subset (↑y : FreeAlgebra ℚ Bool)).mp y.property
    exact h
  have hFxmem : Fx ∈ Submodule.span ℚ
      (Set.range fun idx : Index => MonoidAlgebra.single (zWord idx) (1 : ℚ)) := by
    rw [hdecomp Fx]
    apply Submodule.sum_mem
    intro w hw
    have hwm : w ∈ wordSubmonoidHOne := hsupp w hw
    have hzw : zWord (indexOfHOneWord w) = w := zWord_indexOfHOneWord w hwm
    have hmem : MonoidAlgebra.single w (1 : ℚ) ∈
        Set.range fun idx : Index => MonoidAlgebra.single (zWord idx) (1 : ℚ) :=
      ⟨indexOfHOneWord w,
        congrArg (fun u => MonoidAlgebra.single u (1 : ℚ)) hzw⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  have hfun : (⇑freeAlgEquiv.symm.toLinearMap ∘
        fun idx : Index => MonoidAlgebra.single (zWord idx) (1 : ℚ)) =
        (fun idx : Index => zMonomial idx) := rfl
  have himg : (⇑freeAlgEquiv.symm.toLinearMap) ''
        (Set.range fun idx : Index => MonoidAlgebra.single (zWord idx) (1 : ℚ))
      = Set.range fun idx : Index => zMonomial idx := by
    rw [← Set.range_comp, hfun]
  have hmap : Submodule.map freeAlgEquiv.symm.toLinearMap (Submodule.span ℚ
      (Set.range fun idx : Index => MonoidAlgebra.single (zWord idx) (1 : ℚ)))
      = Submodule.span ℚ (Set.range fun idx : Index => zMonomial idx) := by
    rw [Submodule.map_span, himg]
  have hmem2 : freeAlgEquiv.symm Fx ∈ Submodule.span ℚ
      (Set.range fun idx : Index => zMonomial idx) := by
    rw [← hmap]
    exact Submodule.mem_map.mpr ⟨Fx, hFxmem, rfl⟩
  have hEL : freeAlgEquiv.symm Fx = (↑y : FreeAlgebra ℚ Bool) := by
    rw [hFx]
    exact freeAlgEquiv.symm_apply_apply _
  rwa [hEL] at hmem2

private theorem hspan : (⊤ : Submodule ℚ ↥hOne) ≤ Submodule.span ℚ (Set.range fun idx : Index =>
    (⟨zMonomial idx, zMonomial_mem_hOne idx⟩ : ↥hOne)) := by
  intro y _
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (hx_span y)
  refine Finsupp.mem_span_range_iff_exists_finsupp.mpr ⟨c, ?_⟩
  apply Subtype.ext
  have hcoe : (Submodule.subtype hOne.toSubmodule)
        (c.sum fun i a => a • (⟨zMonomial i, zMonomial_mem_hOne i⟩ : ↥hOne))
      = c.sum (fun i a => a • zMonomial i) := by
    change (Submodule.subtype hOne.toSubmodule (∑ i ∈ c.support, (c i) •
        (⟨zMonomial i, zMonomial_mem_hOne i⟩ : ↥hOne)))
        = (∑ i ∈ c.support, (c i) • zMonomial i)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hsub : (Submodule.subtype hOne.toSubmodule)
        ((⟨zMonomial i, zMonomial_mem_hOne i⟩ : ↥hOne)) = zMonomial i := rfl
    rw [map_smul, hsub]
  change (Submodule.subtype hOne.toSubmodule) (c.sum fun i a => a •
      (⟨zMonomial i, zMonomial_mem_hOne i⟩ : ↥hOne)) = ↑y
  rw [hcoe, hc]

end MetaMathlibExt.MultipleZeta
end

section
namespace MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted

open MetaMathlibExt.MultipleZeta

/-- **Hoffman basis of $\mathfrak{H}^1$.** Let $\mathfrak{H} = \mathbb{Q}\langle x, y \rangle$ be
the free associative $\mathbb{Q}$-algebra on two generators $x$ and $y$, let $\mathfrak{H}^1$ be
the $\mathbb{Q}$-linear span of the empty word and the words ending in $y$ (a subalgebra), and
for each positive integer $k$ let $z_k = x^{k-1} y$. The family of monomials
$z_{k_1} z_{k_2} \cdots z_{k_r}$, indexed by all indices $(k_1, \dots, k_r)$ of positive integers
including the empty index (whose monomial is the empty word $1$), is a basis of $\mathfrak{H}^1$
over $\mathbb{Q}$.

Proves `Wanted` entry `hOne_basis`.

Source: M. E. Hoffman, *The Algebra of Multiple Harmonic Series*, J. Algebra 194
(1997), 477–495, DOI 10.1006/jabr.1997.7127.
-/
theorem hOne_basis :
    ∃ b : Module.Basis Index ℚ ↥hOne,
      ∀ idx : Index, (↑(b idx) : FreeAlgebra ℚ Bool) = zMonomial idx := by
  refine ⟨Module.Basis.mk hliSub hspan, fun idx => ?_⟩
  simp [Module.Basis.mk_apply]

end MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted
