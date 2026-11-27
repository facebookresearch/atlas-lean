/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedWindowTopFunctorExactness

/-!
# Finite iteration of the top quotient

Let `E` be a preadditive exact category with a zero object and binary biproducts. For a fixed
window `[a,b]`, set `u_n=b−n`. The iteration functor `Window E a b ⥤ Window E a u_n` starts at
the identity and repeatedly applies the top quotient, decreasing the upper cutoff by one.

At each step, the single of the current top term includes into the current complex and its
cofiber is the next quotient. These functors preserve the fixed-window cofibrations and
isomorphism weak equivalences. The window length is `L=(b−a+1).toNat`; after `L` steps the
upper cutoff is below `a`, so the terminal complex and its underlying cochain complex are
zero. This also covers reversed windows.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CochainComplex.Bounded

variable (E : Type uE) [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

/-- For a preadditive category `E` and integers `a,b,a',b'` with `a'≤a` and `b≤b'`, `windowInclude
E a b a' b' ha hb : Window E a b ⥤ Window E a' b'` is the full support inclusion. A complex
zero outside `[a,b]` is also zero outside the enlarged interval `[a',b']`. -/
def windowInclude (a b a' b' : ℤ) (ha : a' ≤ a) (hb : b ≤ b') :
    Window E a b ⥤ Window E a' b' :=
  ObjectProperty.ιOfLE (fun K hK j hj => hK j (by
    rcases hj with hj | hj
    · exact Or.inl (lt_of_lt_of_le hj ha)
    · exact Or.inr (lt_of_le_of_lt hb hj)))

omit [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] in
/-- For a preadditive category `E`, `a'≤a`, `b≤b'`, and `K : Window E a b`,
`((windowInclude E a b a' b' ha hb).obj K).obj = K.obj`.
Support enlargement retains the same bounded cochain object. -/
theorem windowInclude_obj (a b a' b' : ℤ) (ha : a' ≤ a) (hb : b ≤ b') (K : Window E a b) :
    ((windowInclude E a b a' b' ha hb).obj K).obj = K.obj := rfl

omit [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] in
/-- For a preadditive category `E`, `a'≤a`, `b≤b'`, and `f:K→L` in `Window E a b`,
`((windowInclude E a b a' b' ha hb).map f).hom = f.hom`.
The bounded cochain map is retained under the full inclusion. -/
theorem windowInclude_map (a b a' b' : ℤ) (ha : a' ≤ a) (hb : b ≤ b')
    {K L : Window E a b} (f : K ⟶ L) :
    ((windowInclude E a b a' b' ha hb).map f).hom = f.hom := rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts and integers
`a,b,a',b'` with `a'≤a` and `b≤b'`, the functor `windowInclude E a b a' b' ha hb` is
Waldhausen exact between the two fixed-window structures. It preserves zero objects,
degreewise admissible cofibrations, isomorphism weak equivalences, and admissible pushouts. -/
theorem windowInclude_isWaldhausenExact (a b a' b' : ℤ) (ha : a' ≤ a) (hb : b ≤ b') :
    @Functor.IsWaldhausenExact (Window E a b) _ _ (windowWaldhausenCategory E a b)
      (Window E a' b') _ _ (windowWaldhausenCategory E a' b')
      (windowInclude E a b a' b' ha hb) := by
  refine @Functor.IsWaldhausenExact.mk (Window E a b) _ _ (windowWaldhausenCategory E a b)
    (Window E a' b') _ _ (windowWaldhausenCategory E a' b')
    (windowInclude E a b a' b' ha hb) ?_ ?_ ?_ ?_
  · intro X hX
    exact IsZero.of_full_of_faithful_of_isZero (windowι E a' b') _
      ((windowι E a b).map_isZero hX)
  · intro X Y f hf
    exact (window_isCofibration_iff E a' b' _).mpr ((window_isCofibration_iff E a b f).mp hf)
  · intro X Y f hf
    let _ : IsIso f := (window_isWeakEquivalence_iff E a b f).mp hf
    exact (window_isWeakEquivalence_iff E a' b' _).mpr inferInstance
  · intro X Y Z P i f inZ inY hi hP
    have hBounded := (windowPushout_ι E a b
      ((window_isCofibration_iff E a b i).mp hi) hP.flip).flip
    exact IsPushout.of_map_of_faithful (windowι E a' b') hBounded

/-- For a preadditive exact category `E` with a zero object and binary biproducts and `a,b : ℤ`,
`windowTopQuotient E a b : Window E a b ⥤ Window E a (b−1)` is Waldhausen exact between the
fixed-window structures. It is the selected top quotient with its proved stricter support
bound, preserving zero objects, cofibrations, weak isomorphisms, and admissible pushouts. -/
theorem windowTopQuotient_isWaldhausenExact (a b : ℤ) :
    @Functor.IsWaldhausenExact (Window E a b) _ _ (windowWaldhausenCategory E a b)
      (Window E a (b - 1)) _ _ (windowWaldhausenCategory E a (b - 1))
      (windowTopQuotient E a b) := by
  refine @Functor.IsWaldhausenExact.mk (Window E a b) _ _ (windowWaldhausenCategory E a b)
    (Window E a (b - 1)) _ _ (windowWaldhausenCategory E a (b - 1))
    (windowTopQuotient E a b) ?_ ?_ ?_ ?_
  · intro X hX
    exact IsZero.of_full_of_faithful_of_isZero (windowι E a (b - 1)) _
      ((windowι E a b).map_isZero (windowTopQuotientFunctor_obj_isZero E a b hX))
  · intro X Y f hf
    exact (window_isCofibration_iff E a (b - 1) _).mpr
      ((window_isCofibration_iff E a b _).mp (windowTopQuotientFunctor_map_isCofibration E a b f hf))
  · intro X Y f hf
    let _ : IsIso f := (window_isWeakEquivalence_iff E a b f).mp hf
    exact (window_isWeakEquivalence_iff E a (b - 1) _).mpr inferInstance
  · intro X Y Z P i f inZ inY hi hP
    have hQ := (windowTopQuotientFunctor_map_isPushout E a b
      ((window_isCofibration_iff E a b i).mp hi) hP.flip).flip
    have hRaw : IsPushout
        ((windowTopQuotientFunctor E a b).map f).hom.hom
        ((windowTopQuotientFunctor E a b).map i).hom.hom
        ((windowTopQuotientFunctor E a b).map inZ).hom.hom
        ((windowTopQuotientFunctor E a b).map inY).hom.hom := by
      have hiQ := (window_isCofibration_iff E a b _).mp
        (windowTopQuotientFunctor_map_isCofibration E a b i hi)
      exact (admissiblePushout_raw E hiQ (windowPushout_ι E a b hiQ hQ.flip)).flip
    exact IsPushout.of_map_of_faithful (windowRaw E a (b - 1)) hRaw

namespace WindowTopIteration

/-- For `b : ℤ`, `cutoff b : ℕ → ℤ` is defined by `cutoff b 0=b` and `cutoff b (n+1)=cutoff b
n−1`. It is the upper support endpoint after `n` top-quotient steps. -/
def cutoff (b : ℤ) : ℕ → ℤ := Nat.rec b (fun _ u => u - 1)

/-- For `b : ℤ` and `n : ℕ`,
`cutoff b n = b−(n : ℤ)`.
Each top quotient decreases the upper support endpoint by one. -/
theorem cutoff_eq (b : ℤ) (n : ℕ) : cutoff b n = b - (n : ℤ) := by
  induction n with
  | zero => simp only [cutoff, Nat.rec_zero, Int.natCast_zero, sub_zero]
  | succ n ih =>
    change cutoff b n - 1 = b - (n + 1 : ℕ)
    rw [ih]
    omega

/-- For a preadditive exact category `E` with a zero object and binary biproducts and `a,b : ℤ`,
`functor E a b n : Window E a b ⥤ Window E a (cutoff b n)` iterates the strict top quotient.
The zero step is the identity, and the successor is the previous functor followed by
`windowTopQuotient E a (cutoff b n)`. -/
def functor (a b : ℤ) : (n : ℕ) → Window E a b ⥤ Window E a (cutoff b n) :=
  Nat.rec (𝟭 (Window E a b)) (fun n F => F ⋙ windowTopQuotient E a (cutoff b n))

/-- For a preadditive exact category `E` with a zero object and binary biproducts and `a,b : ℤ`,
`functor E a b 0 = 𝟭 (Window E a b)`.
The initial window cutoff is `b`. -/
theorem functor_zero (a b : ℤ) : functor E a b 0 = 𝟭 (Window E a b) := rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and `n : ℕ`,
`functor E a b (n+1) = functor E a b n ⋙ windowTopQuotient E a (cutoff b n)`.
The next step quotients the top term at the current upper endpoint. -/
theorem functor_succ (a b : ℤ) (n : ℕ) :
    functor E a b (n + 1) = functor E a b n ⋙ windowTopQuotient E a (cutoff b n) := rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and
`n : ℕ`, `functor E a b n` is Waldhausen exact from the fixed-window structure on `[a,b]` to
that on `[a,cutoff b n]`. Exactness follows by composing the successive strict top-quotient
functors. -/
theorem functor_isWaldhausenExact (a b : ℤ) (n : ℕ) :
    @Functor.IsWaldhausenExact (Window E a b) _ _ (windowWaldhausenCategory E a b)
      (Window E a (cutoff b n)) _ _ (windowWaldhausenCategory E a (cutoff b n))
      (functor E a b n) := by
  induction n with
  | zero =>
    let _ := windowWaldhausenCategory E a b
    exact Functor.IsWaldhausenExact.id
  | succ n ih =>
    exact @Functor.IsWaldhausenExact.comp (Window E a b) _ _ (windowWaldhausenCategory E a b)
      (Window E a (cutoff b n)) _ _ (windowWaldhausenCategory E a (cutoff b n))
      (Window E a (cutoff b n - 1)) _ _ (windowWaldhausenCategory E a (cutoff b n - 1))
      (functor E a b n) (windowTopQuotient E a (cutoff b n)) ih
      (windowTopQuotient_isWaldhausenExact E a (cutoff b n))

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n : ℕ`, and `K : Window E
a b`, the underlying complex of `(functor E a b n).obj K` has zero terms whenever
`j<a ∨ b−(n : ℤ)<j`.
The iteration retains the lower endpoint and decreases the upper endpoint by `n`. -/
theorem support (a b : ℤ) (n : ℕ) (K : Window E a b) :
    ∀ j : ℤ, j < a ∨ b - (n : ℤ) < j → IsZero (((functor E a b n).obj K).obj.obj.X j) := by
  intro j hj
  apply ((functor E a b n).obj K).property j
  rwa [cutoff_eq]

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n :
ℕ`, and `K : Window E a b`, `topSingle E a b n K` is the single of the current quotient's term
at degree `cutoff b n`. It is `(windowTopSingleFunctor E a (cutoff b n)).obj ((functor E a b
n).obj K)`, an object of the current window. -/
abbrev topSingle (a b : ℤ) (n : ℕ) (K : Window E a b) : Window E a (cutoff b n) :=
  (windowTopSingleFunctor E a (cutoff b n)).obj ((functor E a b n).obj K)

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n : ℕ`, and `K : Window E
a b`,
`inclusion E a b n K : topSingle E a b n K ⟶ (functor E a b n).obj K`
is the top-single inclusion in the current window `[a,cutoff b n]`. -/
abbrev inclusion (a b : ℤ) (n : ℕ) (K : Window E a b) :
    topSingle E a b n K ⟶ (functor E a b n).obj K :=
  (windowTopInclusion E a (cutoff b n)).app ((functor E a b n).obj K)

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n :
ℕ`, and `K : Window E a b`, `quotientInOldWindow E a b n K` is the selected quotient of
`(functor E a b n).obj K` by its top single, regarded in `Window E a (cutoff b n)` before
restricting its support to the next window. -/
abbrev quotientInOldWindow (a b : ℤ) (n : ℕ) (K : Window E a b) : Window E a (cutoff b n) :=
  (windowTopQuotientFunctor E a (cutoff b n)).obj ((functor E a b n).obj K)

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n : ℕ`, and `K : Window E
a b`,
`projection E a b n K : (functor E a b n).obj K ⟶ quotientInOldWindow E a b n K`
is the selected top-quotient projection in the current support window. -/
abbrev projection (a b : ℤ) (n : ℕ) (K : Window E a b) :
    (functor E a b n).obj K ⟶ quotientInOldWindow E a b n K :=
  (windowTopQuotientProjection E a (cutoff b n)).app ((functor E a b n).obj K)

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n :
ℕ`, and `K : Window E a b`, the arrows `inclusion E a b n K` and `projection E a b n K` form a
cofiber sequence in `Window E a (cutoff b n)`. It is the selected zero-pushout quotient of the
current top single. -/
theorem isCofiberSequence (a b : ℤ) (n : ℕ) (K : Window E a b) :
    letI := windowWaldhausenCategory E a (cutoff b n)
    IsCofiberSequence (inclusion E a b n K) (projection E a b n K) :=
  windowTopQuotient_isCofiberSequence E a (cutoff b n) ((functor E a b n).obj K)

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n : ℕ`, and `K : Window E
a b`,
`((functor E a b (n+1)).obj K).obj = (quotientInOldWindow E a b n K).obj`.
The next strict-window stage has the same underlying bounded quotient object as the selected quotient in the current
window. -/
theorem successor_obj (a b : ℤ) (n : ℕ) (K : Window E a b) :
    ((functor E a b (n + 1)).obj K).obj = (quotientInOldWindow E a b n K).obj := rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n : ℕ`, and `K : Window E
a b`, put `u_n=cutoff b n`. Then
`(inclusion E a b n K).hom.hom.f u_n = (singleObjXSelf E u_n (((functor E a b n).obj K).obj.obj.X u_n)).hom`.
The supporting component is the single-term isomorphism onto the current top term. -/
theorem inclusion_f_top (a b : ℤ) (n : ℕ) (K : Window E a b) :
    (inclusion E a b n K).hom.hom.f (cutoff b n) =
      (singleObjXSelf E (cutoff b n) (((functor E a b n).obj K).obj.obj.X (cutoff b n))).hom :=
  windowTopInclusion_f_self E a (cutoff b n) ((functor E a b n).obj K)

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n : ℕ`, and `K : Window E
a b`,
`IsZero (((functor E a b (n+1)).obj K).obj.obj.X (cutoff b n))`.
The current top single is quotiented out, so that degree is zero in the successor. -/
theorem successor_top_isZero (a b : ℤ) (n : ℕ) (K : Window E a b) :
    IsZero (((functor E a b (n + 1)).obj K).obj.obj.X (cutoff b n)) :=
  windowTopQuotient_isZero_X_top E a (cutoff b n) ((functor E a b n).obj K)

/-- For `a,b : ℤ`, `length a b = (b−a+1).toNat`. This is the number of descending graded
coordinates in `[a,b]`, and it is zero for a reversed window. -/
def length (a b : ℤ) : ℕ := (b - a + 1).toNat

/-- For `a,b : ℤ`,
`cutoff b (length a b) < a`.
After `(b−a+1).toNat` top-quotient steps, the remaining upper support bound is strictly below the fixed lower support
bound. -/
theorem terminal_upper_lt (a b : ℤ) : cutoff b (length a b) < a := by
  rw [cutoff_eq]
  dsimp only [length]
  omega

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and `K : Window E a b`,
`IsZero ((functor E a b (length a b)).obj K)`.
The terminal quotient is supported in the reversed window `[a,cutoff b (length a b)]`, so every term is zero. -/
theorem terminal_isZero (a b : ℤ) (K : Window E a b) :
    IsZero ((functor E a b (length a b)).obj K) :=
  window_isZero_of_reversed E a (cutoff b (length a b)) (terminal_upper_lt a b) _

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and `K : Window E a b`,
`IsZero (((functor E a b (length a b)).obj K).obj.obj)`.
The full inclusion of the terminal reversed-window zero object into all integer-indexed cochain complexes preserves its
zero property. -/
theorem terminal_raw_isZero (a b : ℤ) (K : Window E a b) :
    IsZero (((functor E a b (length a b)).obj K).obj.obj) :=
  (windowRaw E a (cutoff b (length a b))).map_isZero (terminal_isZero E a b K)

end WindowTopIteration

end CochainComplex.Bounded

end
