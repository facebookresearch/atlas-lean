/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedWindowGradedIteration

/-!
# Suffixes of the supported-single coproduct

Let `E` be a preadditive exact category with a zero object and binary biproducts. Fix `a,b :
ℤ` and `L=(b−a+1).toNat`. A suffix starting at `n` with length `k` and `n+k=L` uses the graded
coordinates `n+i`, for `i : Fin k`, hence the degrees `b−n−i`.

The suffix functor evaluates a window complex in those degrees, places each term in its
supported single complex, and takes their chosen finite coproduct. An empty suffix is the
constant zero functor. A nonempty suffix is the chosen binary coproduct of its head and the
next suffix, in that order. The suffix at `n=0` is exactly `windowGradedEval E a b ⋙
windowGradedCoproduct E a b`; the coordinate families and coproduct functors preserve the
fixed-window structures.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen
open scoped ZeroObject

namespace CochainComplex.Bounded.WindowTopIteration

variable (E : Type uE) [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

/-- For a preadditive exact category `E` with a zero object and binary biproducts, the local
coefficient structure is `ExactCategory.waldhausenCategory E`: cofibrations are admissible
monomorphisms and weak equivalences are isomorphisms. It supplies the coefficient structure
for supported-single suffixes. -/
@[instance_reducible]
local instance suffixExactModel : WaldhausenCategoryWithoutGluing E :=
  ExactCategory.waldhausenCategory E

/-- For a preadditive exact category `E` with a zero object and binary biproducts and `a,b : ℤ`,
the local structure on `Window E a b` is `windowWaldhausenCategory E a b`, with degreewise
admissible monomorphisms as cofibrations and isomorphisms as weak equivalences. -/
@[instance_reducible]
local instance suffixWindowModel (a b : ℤ) : WaldhausenCategoryWithoutGluing (Window E a b) :=
  windowWaldhausenCategory E a b

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and
`k : ℕ`, the local structure on `Fin k → Window E a b` is the pointwise fixed-window
structure. Cofibrations and weak equivalences are tested separately at every suffix
coordinate. -/
@[instance_reducible]
local instance suffixPiModel (a b : ℤ) (k : ℕ) :
    WaldhausenCategoryWithoutGluing (Fin k → Window E a b) :=
  piWaldhausen (fun _ : Fin k => Window E a b)

omit [Category E] [Preadditive E] [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] in
/-- For `a,b : ℤ`, set `L=(b−a+1).toNat`. If `n,k : ℕ` satisfy `h : n+k=L`, then
`originalGradedSuffixCoordinate a b n k h : Fin k → Fin L` sends `i` to the coordinate with
value `n+i.val`. The equality `n+k=L` supplies its upper bound. -/
def originalGradedSuffixCoordinate (a b : ℤ) (n k : ℕ) (h : n + k = length a b)
    (i : Fin k) : Fin (length a b) :=
  ⟨n + i.val, by have hi := i.isLt; omega⟩

omit [Category E] [Preadditive E] [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] in
/-- For `a,b : ℤ`, set `L=(b−a+1).toNat`. For every `i : Fin L`,
`originalGradedSuffixCoordinate a b 0 L (Nat.zero_add L) i = i`.
The suffix beginning at zero uses the entire coordinate family without an offset. -/
theorem originalGradedSuffixCoordinate_zero (a b : ℤ) (i : Fin (length a b)) :
    originalGradedSuffixCoordinate a b 0 (length a b) (Nat.zero_add _) i = i := by
  apply Fin.ext
  exact Nat.zero_add _

omit [Category E] [Preadditive E] [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] in
/-- For `a,b : ℤ`, `L=(b−a+1).toNat`, and `n,k : ℕ` with `n+(k+1)=L`, the first coordinate of the suffix is `n`:
`originalGradedSuffixCoordinate a b n (k+1) h 0 = ⟨n, _⟩`.
The hypothesis ensures `n<L`. -/
theorem originalGradedSuffixCoordinate_head (a b : ℤ) (n k : ℕ)
    (h : n + (k + 1) = length a b) :
    originalGradedSuffixCoordinate a b n (k + 1) h 0 = ⟨n, by omega⟩ := by
  apply Fin.ext
  exact Nat.add_zero _

omit [Category E] [Preadditive E] [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] in
/-- For `a,b : ℤ`, `L=(b−a+1).toNat`, `n,k : ℕ` with `h : n+(k+1)=L`, and `i : Fin k`,
`originalGradedSuffixCoordinate a b n (k+1) h i.succ = originalGradedSuffixCoordinate a b (n+1) k h' i`,
where `h' : (n+1)+k=L` follows from `h`. Both coordinates have value `n+1+i.val`. -/
theorem originalGradedSuffixCoordinate_tail (a b : ℤ) (n k : ℕ)
    (h : n + (k + 1) = length a b) (i : Fin k) :
    originalGradedSuffixCoordinate a b n (k + 1) h i.succ =
      originalGradedSuffixCoordinate a b (n + 1) k (by omega) i := by
  apply Fin.ext
  dsimp only [originalGradedSuffixCoordinate, Fin.val_succ]
  omega

/-- For a preadditive category `E` with a zero object, `a,b : ℤ`, `L=(b−a+1).toNat`, and `n<L`,
the endofunctor `originalGradedHead E a b n hn` on `Window E a b` evaluates a complex in
degree `b−n` and places that term in a single complex supported at the same degree. -/
def originalGradedHead (a b : ℤ) (n : ℕ) (hn : n < length a b) :
    Window E a b ⥤ Window E a b :=
  windowEval E a b (windowGradedDegree a b ⟨n, hn⟩) ⋙
    windowGradedSingle E a b ⟨n, hn⟩

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and `n<length a b`, there
is a natural isomorphism
`originalGradedHead E a b n hn ≅ originalTopFunctor E a b n`.
The left side is the supported single of the input term at `b−n`; the right side is the supported top single after `n`
top quotients, included in the input window. -/
def originalGradedHeadTopIso (a b : ℤ) (n : ℕ) (hn : n < length a b) :
    originalGradedHead E a b n hn ≅ originalTopFunctor E a b n :=
  originalGradedTopFunctorIso E a b n hn

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and
`n<length a b`, `originalGradedHead E a b n hn` is Waldhausen exact on the fixed-window
structure. It is evaluation in degree `b−n` followed by the supported single embedding, and
therefore preserves zero objects, cofibrations, isomorphism weak equivalences, and admissible
pushouts. -/
theorem originalGradedHead_isWaldhausenExact (a b : ℤ) (n : ℕ)
    (hn : n < length a b) :
    (originalGradedHead E a b n hn).IsWaldhausenExact :=
  (windowEval_isWaldhausenExact E a b (windowGradedDegree a b ⟨n, hn⟩)).comp
    (windowGradedSingle_isWaldhausenExact E a b ⟨n, hn⟩)

/-- For a preadditive category `E` with a zero object, `a,b : ℤ`, and `n,k : ℕ` with
`n+k=L=(b−a+1).toNat`, the functor `originalGradedSuffixFamily E a b n k h : Window E a b ⥤
(Fin k → Window E a b)` sends a complex to its terms in degrees `b−n−i`, each placed in a
single complex supported at that degree. -/
def originalGradedSuffixFamily (a b : ℤ) (n k : ℕ) (h : n + k = length a b) :
    Window E a b ⥤ (Fin k → Window E a b) :=
  Functor.pi' (fun i =>
    windowEval E a b (windowGradedDegree a b (originalGradedSuffixCoordinate a b n k h i)) ⋙
      windowGradedSingle E a b (originalGradedSuffixCoordinate a b n k h i))

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and
`n,k : ℕ` with `n+k=L=(b−a+1).toNat`, the endofunctor `originalGradedSuffix E a b n k h` takes
`originalGradedSuffixFamily E a b n k h` and applies the chosen `k`-fold coproduct functor in
`Window E a b`. It assembles the supported singles in coordinate order `n,n+1,…,L−1`. -/
def originalGradedSuffix (a b : ℤ) (n k : ℕ) (h : n + k = length a b) :
    Window E a b ⥤ Window E a b :=
  originalGradedSuffixFamily E a b n k h ⋙ waldhausenFinCoproductFunctor (Window E a b) k

omit [HasBinaryBiproducts E] [ExactCategory E] in
/-- For a preadditive category `E` with a zero object and `a,b : ℤ`, put `L=(b−a+1).toNat`. Then
`originalGradedSuffixFamily E a b 0 L (Nat.zero_add L) = windowGradedEval E a b ⋙ windowGradedSingleFamily E a b`.
The full suffix uses all graded evaluations and their supported single-degree embeddings. -/
theorem originalGradedSuffixFamily_zero (a b : ℤ) :
    originalGradedSuffixFamily E a b 0 (length a b) (Nat.zero_add _) =
      windowGradedEval E a b ⋙ windowGradedSingleFamily E a b := by
  apply Functor.pi_ext
  intro i
  change (windowEval E a b
    (windowGradedDegree a b (originalGradedSuffixCoordinate a b 0 (length a b)
      (Nat.zero_add _) i)) ⋙
    windowGradedSingle E a b (originalGradedSuffixCoordinate a b 0 (length a b)
      (Nat.zero_add _) i)) = _
  rw [originalGradedSuffixCoordinate_zero]
  rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts and `a,b : ℤ`, put `L=(b−a+1).toNat`.
Then
`originalGradedSuffix E a b 0 L (Nat.zero_add L) = windowGradedEval E a b ⋙ windowGradedCoproduct E a b`.
This is an equality of endofunctors on the fixed-window category. -/
theorem originalGradedSuffix_zero_eq (a b : ℤ) :
    originalGradedSuffix E a b 0 (length a b) (Nat.zero_add _) =
      windowGradedEval E a b ⋙ windowGradedCoproduct E a b := by
  rw [originalGradedSuffix, originalGradedSuffixFamily_zero]
  rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and `n : ℕ` with
`n+0=length a b`,
`originalGradedSuffix E a b n 0 h = (Functor.const (Window E a b)).obj (0 : Window E a b)`.
The zero-length coproduct is the selected zero window object. -/
theorem originalGradedSuffix_terminal (a b : ℤ) (n : ℕ) (h : n + 0 = length a b) :
    originalGradedSuffix E a b n 0 h =
      (Functor.const (Window E a b)).obj (0 : Window E a b) := rfl

omit [HasBinaryBiproducts E] [ExactCategory E] in
/-- For a preadditive category `E` with a zero object, `a,b : ℤ`, and `n,k : ℕ` with `n+(k+1)=length a b`,
`originalGradedSuffixFamily E a b n (k+1) h ⋙ Pi.eval (fun _ : Fin (k+1) => Window E a b) 0 = originalGradedHead E a b n
hn`,
where `hn : n<length a b` follows from the length equality. The first coordinate is the single of the term in degree
`b−n`. -/
theorem originalGradedSuffixFamily_head (a b : ℤ) (n k : ℕ)
    (h : n + (k + 1) = length a b) :
    originalGradedSuffixFamily E a b n (k + 1) h ⋙
      Pi.eval (fun _ : Fin (k + 1) => Window E a b) 0 =
        originalGradedHead E a b n (by omega) := by
  change (windowEval E a b
    (windowGradedDegree a b (originalGradedSuffixCoordinate a b n (k + 1) h 0)) ⋙
    windowGradedSingle E a b (originalGradedSuffixCoordinate a b n (k + 1) h 0)) = _
  rw [originalGradedSuffixCoordinate_head]
  rfl

omit [HasBinaryBiproducts E] [ExactCategory E] in
/-- For a preadditive category `E` with a zero object, `a,b : ℤ`, and `n,k : ℕ` with `n+(k+1)=length a b`,
`originalGradedSuffixFamily E a b n (k+1) h ⋙ finTail (Window E a b) k = originalGradedSuffixFamily E a b (n+1) k h'`,
where `h' : (n+1)+k=length a b`. Dropping the first family coordinate leaves exactly the next suffix. -/
theorem originalGradedSuffixFamily_tail (a b : ℤ) (n k : ℕ)
    (h : n + (k + 1) = length a b) :
    originalGradedSuffixFamily E a b n (k + 1) h ⋙ finTail (Window E a b) k =
      originalGradedSuffixFamily E a b (n + 1) k (by omega) := by
  apply Functor.pi_ext
  intro i
  change (windowEval E a b
    (windowGradedDegree a b (originalGradedSuffixCoordinate a b n (k + 1) h i.succ)) ⋙
    windowGradedSingle E a b (originalGradedSuffixCoordinate a b n (k + 1) h i.succ)) = _
  rw [originalGradedSuffixCoordinate_tail]
  rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and `n,k : ℕ` with
`n+(k+1)=length a b`,
`originalGradedSuffix E a b n (k+1) h = (originalGradedHead E a b n hn).prod' (originalGradedSuffix E a b (n+1) k h') ⋙
waldhausenCoproductFunctor (Window E a b)`.
The equality uses the head first and the remaining suffix second in the chosen binary coproduct. -/
theorem originalGradedSuffix_succ (a b : ℤ) (n k : ℕ)
    (h : n + (k + 1) = length a b) :
    originalGradedSuffix E a b n (k + 1) h =
      ((originalGradedHead E a b n (by omega)).prod'
        (originalGradedSuffix E a b (n + 1) k (by omega))) ⋙
          waldhausenCoproductFunctor (Window E a b) := by
  unfold originalGradedSuffix
  rw [waldhausenFinCoproductFunctor_succ]
  have hPair : originalGradedSuffixFamily E a b n (k + 1) h ⋙
      (Pi.eval (fun _ : Fin (k + 1) => Window E a b) 0).prod'
        (finTail (Window E a b) k ⋙ waldhausenFinCoproductFunctor (Window E a b) k) =
      (originalGradedHead E a b n (by omega)).prod'
        (originalGradedSuffixFamily E a b (n + 1) k (by omega) ⋙
          waldhausenFinCoproductFunctor (Window E a b) k) := by
    change ((originalGradedSuffixFamily E a b n (k + 1) h ⋙
      Pi.eval (fun _ : Fin (k + 1) => Window E a b) 0).prod'
      ((originalGradedSuffixFamily E a b n (k + 1) h ⋙ finTail (Window E a b) k) ⋙
        waldhausenFinCoproductFunctor (Window E a b) k)) = _
    rw [originalGradedSuffixFamily_head, originalGradedSuffixFamily_tail]
  exact congrArg (fun F => F ⋙ waldhausenCoproductFunctor (Window E a b)) hPair

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and
`n,k : ℕ` with `n+k=length a b`, `originalGradedSuffixFamily E a b n k h` is Waldhausen exact
from the fixed-window structure to its pointwise family structure. Each coordinate is window
evaluation followed by a supported single-degree embedding. -/
theorem originalGradedSuffixFamily_isWaldhausenExact (a b : ℤ) (n k : ℕ)
    (h : n + k = length a b) :
    (originalGradedSuffixFamily E a b n k h).IsWaldhausenExact :=
  Functor.IsWaldhausenExact.pi' (fun _ : Fin k => Window E a b) _
    (fun i =>
      (windowEval_isWaldhausenExact E a b
        (windowGradedDegree a b (originalGradedSuffixCoordinate a b n k h i))).comp
        (windowGradedSingle_isWaldhausenExact E a b
          (originalGradedSuffixCoordinate a b n k h i)))

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and
`n,k : ℕ` with `n+k=length a b`, the endofunctor `originalGradedSuffix E a b n k h` is
Waldhausen exact on the fixed-window structure. The supported-single family is exact, and the
chosen finite coproduct is exact using the gluing axiom `windowGluing E a b`. -/
theorem originalGradedSuffix_isWaldhausenExact (a b : ℤ) (n k : ℕ)
    (h : n + k = length a b) : (originalGradedSuffix E a b n k h).IsWaldhausenExact :=
  (originalGradedSuffixFamily_isWaldhausenExact E a b n k h).comp
    (waldhausenFinCoproductFunctor_isWaldhausenExact (Window E a b)
      (windowGluing E a b) k)

end CochainComplex.Bounded.WindowTopIteration

end
