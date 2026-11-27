/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Cyclic

/-!
# Endpoint multiplication and adjacent word multiplication

For a type A with multiplication, outerWord multiplies the first entry of a word on the left and
the last entry on the right, leaving every internal entry unchanged. If multiplication is
associative, this operation commutes with each adjacent multiplication in the bar differential.
-/
@[expose] public section

namespace ModuleCat.Algebra.Hochschild
universe v
variable {A : Type v}

/-- For a type A with multiplication, n : ℕ, l,r ∈ A and a word a = (a₀,…,aₙ₊₁), outerWord n l r a
is (l·a₀,a₁,…,aₙ,aₙ₊₁·r). Its length remains n+2 and its n internal entries are unchanged. -/
def outerWord [Mul A] (n : ℕ) (l r : A) (a : Fin (n + 2) → A) : Fin (n + 2) → A :=
  Fin.cons (l * a 0) (Fin.snoc (Fin.init (Fin.tail a)) (a (Fin.last (n + 1)) * r))

/-- For any multiplication on A, n : ℕ, endpoints a₀,aLast and an internal word a of length n,
outerWord n l r (a₀,a,aLast) = (l·a₀,a,aLast·r). No associativity hypothesis is needed for this
formula. -/
theorem outerWord_cons_snoc [Mul A] (n : ℕ) (l r a₀ aLast : A) (a : Fin n → A) :
    outerWord n l r (Fin.cons a₀ (Fin.snoc a aLast)) =
      Fin.cons (l * a₀) (Fin.snoc a (aLast * r)) := by
  simp only [outerWord, Fin.cons_zero, Fin.tail_cons, Fin.cons_last,
    Fin.init_snoc, Fin.snoc_last]

private theorem tail_snoc (n : ℕ) (a : Fin (n + 1) → A) (b : A) :
    Fin.tail (Fin.snoc (α := fun _ : Fin (n + 2) => A) a b) =
      Fin.snoc (α := fun _ : Fin (n + 1) => A) (Fin.tail a) b := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change (Fin.snoc (α := fun _ : Fin (n + 2) => A) a b) (Fin.last (n + 1)) =
      (Fin.snoc (α := fun _ : Fin (n + 1) => A) (Fin.tail a) b) (Fin.last n)
    simp only [Fin.snoc_last]
  · change (Fin.snoc (α := fun _ : Fin (n + 2) => A) a b) j.succ.castSucc =
      (Fin.snoc (α := fun _ : Fin (n + 1) => A) (Fin.tail a) b) j.castSucc
    simp only [Fin.snoc_castSucc]
    rfl

private theorem snoc_zero_value (n : ℕ) (a : Fin (n + 1) → A) (b : A) :
    (Fin.snoc (α := fun _ : Fin (n + 2) => A) a b) 0 = a 0 := by
  change (Fin.snoc (α := fun _ : Fin (n + 2) => A) a b) (0 : Fin (n + 1)).castSucc = a 0
  simp only [Fin.snoc_castSucc]

private theorem merge_outerWord_cons_snoc [Semigroup A] (n : ℕ) (i : Fin (n + 2))
    (l r a₀ aLast : A) (a : Fin (n + 1) → A) :
    hochschildMulAdjacent i (outerWord (n + 1) l r (Fin.cons a₀ (Fin.snoc a aLast))) =
      outerWord n l r (hochschildMulAdjacent i (Fin.cons a₀ (Fin.snoc a aLast))) := by
  rw [outerWord_cons_snoc]
  cases i using Fin.cases with
  | zero =>
      rw [mulAdjacent_cons_zero, mulAdjacent_cons_zero]
      change Fin.cons ((l * a₀) *
          (Fin.snoc (α := fun _ : Fin (n + 2) => A) a (aLast * r)) 0)
          (Fin.tail (Fin.snoc (α := fun _ : Fin (n + 2) => A) a (aLast * r))) =
        outerWord n l r (Fin.cons
          (a₀ * (Fin.snoc (α := fun _ : Fin (n + 2) => A) a aLast) 0)
          (Fin.tail (Fin.snoc (α := fun _ : Fin (n + 2) => A) a aLast)))
      rw [snoc_zero_value, snoc_zero_value, tail_snoc, tail_snoc, outerWord_cons_snoc]
      simp only [mul_assoc]
  | succ i =>
      rw [mulAdjacent_cons_succ, mulAdjacent_cons_succ]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [hochschildMulAdjacent_last_snoc, hochschildMulAdjacent_last_snoc]
        have hlast : (Fin.last n).succ = Fin.last (n + 1) := rfl
        simp only [Fin.init_snoc, Fin.snoc_castSucc, hlast, Fin.snoc_last,
          outerWord_cons_snoc, mul_assoc]
      · rw [hochschildMulAdjacent_castSucc_snoc, hochschildMulAdjacent_castSucc_snoc]
        simp only [Fin.init_snoc, Fin.snoc_last, outerWord_cons_snoc]

/-- Let A be a semigroup. For n : ℕ, an adjacent position i ∈ Fin(n+2), l,r ∈ A and a word a of
length n+3, multiplying entries i and i+1 after outerWord (n+1) l r gives the same word as
applying outerWord n l r after that adjacent multiplication. -/
theorem mulAdjacent_outerWord [Semigroup A] (n : ℕ) (i : Fin (n + 2)) (l r : A)
    (a : Fin (n + 3) → A) :
    hochschildMulAdjacent i (outerWord (n + 1) l r a) =
      outerWord n l r (hochschildMulAdjacent i a) := by
  simpa only [Fin.snoc_init_self, Fin.cons_self_tail] using
    merge_outerWord_cons_snoc n i l r (a 0) ((Fin.tail a) (Fin.last (n + 1)))
      (Fin.init (Fin.tail a))

end ModuleCat.Algebra.Hochschild
