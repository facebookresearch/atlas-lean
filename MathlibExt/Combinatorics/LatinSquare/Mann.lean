/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Logic.Equiv.Basic

/-!
# Mann's product criterion for orthogonal Latin squares

This file proves that two finite Latin squares are orthogonal exactly when the
rowwise product of the first square with the inverse of the second is Latin.
Rows are viewed as permutations and composed right-to-left.

The statement follows H. B. Mann, "The construction of orthogonal Latin
squares", *Annals of Mathematical Statistics* 13 (1942), 418–423, as restated
by O. Zaikin, E. Vatutin, and C. Bright in
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Zaikin/zaikin4.tex>, lines 112, 127,
345–349, and 386–389.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Mann's product criterion for orthogonal Latin squares.** Let $n$ be a natural number,
write $[n] = \{0, \dots, n-1\}$, and let $A$ and $B$ be Latin squares of order $n$ with rows,
columns and entries indexed by $[n]$: every row and every column of each square is a bijection
of $[n]$. For a row index $i$ write $A_i$ and $B_i$ for the permutations $j \mapsto A_{ij}$ and
$j \mapsto B_{ij}$ of $[n]$. Then the map $(i, j) \mapsto (A_{ij}, B_{ij})$ is a bijection of
$[n] \times [n]$ (that is, $A$ and $B$ are orthogonal) if and only if the square $C$ with
entries $C_{ij} = A_i(B_i^{-1}(j))$ is a Latin square, meaning that every row $j \mapsto C_{ij}$
and every column $i \mapsto C_{ij}$ of $C$ is a bijection of $[n]$.

The equivalence uses only the row conditions on $A$ and $B$; the column conditions are kept so
that both inputs are Latin squares. The row condition on $C$ follows from the row conditions on
$A$ and $B$, and is included so that the right side is the full Latin-square condition. -/
theorem mann_product_criterion_for_orthogonal_latin_squares
    {n : ℕ} (A B : Fin n → Fin n → Fin n)
    (hArow : ∀ i, Function.Bijective (A i))
    (_hAcol : ∀ j, Function.Bijective (fun i => A i j))
    (hBrow : ∀ i, Function.Bijective (B i))
    (_hBcol : ∀ j, Function.Bijective (fun i => B i j)) :
    Function.Bijective (fun ij : Fin n × Fin n => (A ij.1 ij.2, B ij.1 ij.2)) ↔
      ((∀ i, Function.Bijective
          (fun j => A i ((Equiv.ofBijective (B i) (hBrow i)).symm j))) ∧
        ∀ j, Function.Bijective
          (fun i => A i ((Equiv.ofBijective (B i) (hBrow i)).symm j))) := by
  have hP : ∀ i, Function.Bijective
      (fun j => A i ((Equiv.ofBijective (B i) (hBrow i)).symm j)) := by
    intro i
    exact (hArow i).comp (Equiv.ofBijective (B i) (hBrow i)).symm.bijective
  have cancel : ∀ (i : Fin n) (j : Fin n),
      (Equiv.ofBijective (B i) (hBrow i)).symm (B i j) = j :=
    fun i j => Equiv.symm_apply_apply _ j
  have hPhi : Function.Bijective
      (fun ij : Fin n × Fin n => (ij.1, B ij.1 ij.2)) := by
    refine ⟨?_, ?_⟩
    · intro x y h
      obtain ⟨i1, j1⟩ := x
      obtain ⟨i2, j2⟩ := y
      have h' : (i1, B i1 j1) = (i2, B i2 j2) := h
      have h1 : i1 = i2 := congrArg Prod.fst h'
      have h2 : B i1 j1 = B i2 j2 := congrArg Prod.snd h'
      subst i2
      have hj : j1 = j2 := (hBrow i1).1 h2
      subst hj
      rfl
    · intro y
      obtain ⟨i, k⟩ := y
      obtain ⟨j, hj⟩ := (hBrow i).2 k
      refine ⟨(i, j), ?_⟩
      have hpair : (i, B i j) = (i, k) := by rw [hj]
      exact hpair
  have hEq : (fun ij : Fin n × Fin n => (A ij.1 ij.2, B ij.1 ij.2)) =
      (fun p : Fin n × Fin n =>
        (A p.1 ((Equiv.ofBijective (B p.1) (hBrow p.1)).symm p.2), p.2)) ∘
      (fun ij : Fin n × Fin n => (ij.1, B ij.1 ij.2)) := by
    apply funext
    intro ij
    obtain ⟨i, j⟩ := ij
    simp only [Function.comp_apply]
    change (A i j, B i j) =
      (A i ((Equiv.ofBijective (B i) (hBrow i)).symm (B i j)), B i j)
    rw [cancel i j]
  have hTransfer : Function.Bijective
      (fun ij : Fin n × Fin n => (A ij.1 ij.2, B ij.1 ij.2)) ↔
      Function.Bijective
        (fun p : Fin n × Fin n =>
          (A p.1 ((Equiv.ofBijective (B p.1) (hBrow p.1)).symm p.2), p.2)) := by
    rw [hEq]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro x1 x2 hx
        obtain ⟨y1, rfl⟩ := hPhi.2 x1
        obtain ⟨y2, rfl⟩ := hPhi.2 x2
        have heq : ((fun p : Fin n × Fin n =>
          (A p.1 ((Equiv.ofBijective (B p.1) (hBrow p.1)).symm p.2), p.2)) ∘
          (fun ij : Fin n × Fin n => (ij.1, B ij.1 ij.2))) y1 =
          ((fun p : Fin n × Fin n =>
          (A p.1 ((Equiv.ofBijective (B p.1) (hBrow p.1)).symm p.2), p.2)) ∘
          (fun ij : Fin n × Fin n => (ij.1, B ij.1 ij.2))) y2 := hx
        have hy : y1 = y2 := h.1 heq
        rw [hy]
      · intro y
        obtain ⟨z, hz⟩ := h.2 y
        exact ⟨(fun ij : Fin n × Fin n => (ij.1, B ij.1 ij.2)) z, hz⟩
    · intro h
      exact h.comp hPhi
  have hPsi_iff : Function.Bijective
        (fun p : Fin n × Fin n =>
          (A p.1 ((Equiv.ofBijective (B p.1) (hBrow p.1)).symm p.2), p.2)) ↔
      (∀ j, Function.Bijective
        (fun i => A i ((Equiv.ofBijective (B i) (hBrow i)).symm j))) := by
    constructor
    · intro h j
      refine ⟨?_, ?_⟩
      · intro i1 i2 hi
        have hi' : A i1 ((Equiv.ofBijective (B i1) (hBrow i1)).symm j) =
            A i2 ((Equiv.ofBijective (B i2) (hBrow i2)).symm j) := hi
        have heq : (fun p : Fin n × Fin n =>
            (A p.1 ((Equiv.ofBijective (B p.1) (hBrow p.1)).symm p.2), p.2))
            (i1, j) =
            (fun p : Fin n × Fin n =>
            (A p.1 ((Equiv.ofBijective (B p.1) (hBrow p.1)).symm p.2), p.2))
            (i2, j) := by
          change (A i1 ((Equiv.ofBijective (B i1) (hBrow i1)).symm j), j) =
            (A i2 ((Equiv.ofBijective (B i2) (hBrow i2)).symm j), j)
          rw [hi']
        have hpair := h.1 heq
        exact congrArg Prod.fst hpair
      · intro a
        obtain ⟨p, hp⟩ := h.2 (a, j)
        obtain ⟨i, k⟩ := p
        have hp' : (A i ((Equiv.ofBijective (B i) (hBrow i)).symm k), k) =
            (a, j) := hp
        have hk : k = j := congrArg Prod.snd hp'
        subst k
        have ha : A i ((Equiv.ofBijective (B i) (hBrow i)).symm j) = a :=
          congrArg Prod.fst hp'
        exact ⟨i, ha⟩
    · intro h
      refine ⟨?_, ?_⟩
      · intro x1 x2 hx
        obtain ⟨i1, k1⟩ := x1
        obtain ⟨i2, k2⟩ := x2
        have hx' : (A i1 ((Equiv.ofBijective (B i1) (hBrow i1)).symm k1), k1) =
            (A i2 ((Equiv.ofBijective (B i2) (hBrow i2)).symm k2), k2) := hx
        have hk : k1 = k2 := congrArg Prod.snd hx'
        subst k1
        have ha : A i1 ((Equiv.ofBijective (B i1) (hBrow i1)).symm k2) =
            A i2 ((Equiv.ofBijective (B i2) (hBrow i2)).symm k2) :=
          congrArg Prod.fst hx'
        have hi : i1 = i2 := (h k2).1 ha
        subst i1
        rfl
      · intro y
        obtain ⟨a, b⟩ := y
        obtain ⟨i, hi⟩ := (h b).2 a
        have hi' : A i ((Equiv.ofBijective (B i) (hBrow i)).symm b) = a := hi
        refine ⟨(i, b), ?_⟩
        have hpair : (A i ((Equiv.ofBijective (B i) (hBrow i)).symm b), b) =
            (a, b) := by rw [hi']
        exact hpair
  constructor
  · intro hF
    exact ⟨hP, hPsi_iff.mp (hTransfer.mp hF)⟩
  · intro h
    exact hTransfer.mpr (hPsi_iff.mpr h.2)

end MetaMathlibExt
