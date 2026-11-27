/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedWindowGradedCoproduct
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberFunctorSequenceComposition
public import Mathlib.CategoryTheory.Whiskering

/-!
# Quotient iterations inside a fixed cochain window

Let `E` be a preadditive exact category with a zero object and binary biproducts, and fix `a,b
: ℤ`. After `n` top quotients, the cutoff is `u_n=b−n` and the complex lies in `Window E a
u_n`. Including this smaller window into `Window E a b` gives an endofunctor `Q_n`, with
natural projections `Q_n ⟶ Q_{n+1}` and `𝟭 ⟶ Q_n`.

The component of the composed projection in any degree `j≤u_n` is an isomorphism. At a
nonterminal step `n<(b−a+1).toNat`, the input term in degree `u_n`, placed in a supported
single, is naturally isomorphic to the top single of `Q_n`. These top singles, quotient
projections, and inclusions give a cofiber functor sequence `Top_n ⟶ Q_n ⟶ Q_{n+1}` in the
common window. The endofunctor at the terminal length sends every complex to zero.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.SConstruction
open scoped ZeroObject

namespace CochainComplex.Bounded.WindowTopIteration

variable (E : Type uE) [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

/-- For a preadditive exact category `E` with a zero object and binary biproducts and `a,b : ℤ`,
the local structure on `Window E a b` is `windowWaldhausenCategory E a b`, with degreewise
admissible monomorphisms as cofibrations and isomorphisms as weak equivalences. -/
@[instance_reducible]
local instance originalWindowModel (a b : ℤ) : WaldhausenCategoryWithoutGluing (Window E a b) :=
  windowWaldhausenCategory E a b

/-- For `b : ℤ` and `n : ℕ`, `cutoff b n ≤ b`. Since `cutoff b n = b−(n : ℤ)`, each quotient
iteration weakly decreases the upper support bound. -/
theorem cutoff_le (b : ℤ) (n : ℕ) : cutoff b n ≤ b := by
  rw [cutoff_eq]
  omega

/-- For a preadditive category `E`, `a,b : ℤ`, and `n : ℕ`, the functor `includeOriginal E a b n :
Window E a (cutoff b n) ⥤ Window E a b` is support enlargement along `cutoff b n ≤ b`. It
includes the complex supported in the smaller window without changing its cochain object. -/
def includeOriginal (a b : ℤ) (n : ℕ) : Window E a (cutoff b n) ⥤ Window E a b :=
  windowInclude E a (cutoff b n) a b le_rfl (cutoff_le b n)

omit [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] in
/-- For a preadditive category `E`, `a,b : ℤ`, `n : ℕ`, and `K : Window E a (cutoff b n)`,
`((includeOriginal E a b n).obj K).obj = K.obj`.
The inclusion retains the bounded cochain object. -/
theorem includeOriginal_obj (a b : ℤ) (n : ℕ) (K : Window E a (cutoff b n)) :
    ((includeOriginal E a b n).obj K).obj = K.obj := rfl

omit [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] in
/-- For a preadditive category `E`, `a,b : ℤ`, `n : ℕ`, and `f : K ⟶ L` in `Window E a (cutoff b n)`,
`((includeOriginal E a b n).map f).hom = f.hom`.
The underlying bounded cochain map is unchanged by support enlargement. -/
theorem includeOriginal_map (a b : ℤ) (n : ℕ)
    {K L : Window E a (cutoff b n)} (f : K ⟶ L) :
    ((includeOriginal E a b n).map f).hom = f.hom := rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and
`n : ℕ`, `includeOriginal E a b n` is Waldhausen exact between the fixed-window structures on
`[a,cutoff b n]` and `[a,b]`. It preserves zero objects, degreewise admissible cofibrations,
isomorphism weak equivalences, and admissible pushouts. -/
theorem includeOriginal_isWaldhausenExact (a b : ℤ) (n : ℕ) :
    (includeOriginal E a b n).IsWaldhausenExact :=
  windowInclude_isWaldhausenExact E a (cutoff b n) a b le_rfl (cutoff_le b n)

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and `n : ℕ`,
`originalFunctor E a b n = functor E a b n ⋙ includeOriginal E a b n`.
It performs `n` successive top quotients and views the result, supported in `[a,b−n]`, as an object of `Window E a b`.
-/
def originalFunctor (a b : ℤ) (n : ℕ) : Window E a b ⥤ Window E a b :=
  functor E a b n ⋙ includeOriginal E a b n

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n : ℕ`, and `K : Window E
a b`,
`((originalFunctor E a b n).obj K).obj = ((functor E a b n).obj K).obj`.
The inclusion back into the input window retains the bounded quotient object. -/
theorem originalFunctor_obj (a b : ℤ) (n : ℕ) (K : Window E a b) :
    ((originalFunctor E a b n).obj K).obj = ((functor E a b n).obj K).obj := rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n : ℕ`, and a window map
`f : K ⟶ L`,
`((originalFunctor E a b n).map f).hom = ((functor E a b n).map f).hom`.
The iterated quotient map is retained when its support window is enlarged. -/
theorem originalFunctor_map (a b : ℤ) (n : ℕ) {K L : Window E a b} (f : K ⟶ L) :
    ((originalFunctor E a b n).map f).hom = ((functor E a b n).map f).hom := rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts and `a,b : ℤ`,
`originalFunctor E a b 0 = 𝟭 (Window E a b)`.
At step zero the cutoff is `b`, and the included quotient iteration is the identity functor. -/
theorem originalFunctor_zero (a b : ℤ) : originalFunctor E a b 0 = 𝟭 (Window E a b) := rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and
`n : ℕ`, `originalFunctor E a b n` is Waldhausen exact on `Window E a b`. The iterated top
quotient is exact into its smaller support window, and the inclusion into the input window is
exact. -/
theorem originalFunctor_isWaldhausenExact (a b : ℤ) (n : ℕ) :
    (originalFunctor E a b n).IsWaldhausenExact :=
  (functor_isWaldhausenExact E a b n).comp (includeOriginal_isWaldhausenExact E a b n)

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and `n : ℕ`,
`originalFunctor E a b (n+1) = functor E a b n ⋙ windowTopQuotientFunctor E a (cutoff b n) ⋙ includeOriginal E a b n`.
The successor applies the chosen top quotient in the current window and then includes its underlying object into
`[a,b]`. -/
theorem originalFunctor_succ (a b : ℤ) (n : ℕ) :
    originalFunctor E a b (n + 1) =
      functor E a b n ⋙ windowTopQuotientFunctor E a (cutoff b n) ⋙
        includeOriginal E a b n := rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and
`n : ℕ`, the natural transformation `originalProjectionStep E a b n` goes from
`originalFunctor E a b n` to `originalFunctor E a b (n+1)`. At `K : Window E a b`, its
underlying bounded map is the selected top-quotient projection `projection E a b n K`. -/
def originalProjectionStep (a b : ℤ) (n : ℕ) :
    originalFunctor E a b n ⟶ originalFunctor E a b (n + 1) where
  app K := ObjectProperty.homMk (projection E a b n K).hom
  naturality {K L} f := by
    apply ObjectProperty.hom_ext
    exact congrArg (fun g => g.hom)
      ((windowTopQuotientProjection E a (cutoff b n)).naturality ((functor E a b n).map f))

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n : ℕ`, and `K : Window E
a b`,
`((originalProjectionStep E a b n).app K).hom = (projection E a b n K).hom`.
Including the quotient step into the common input window retains its bounded cochain map. -/
theorem originalProjectionStep_app_hom (a b : ℤ) (n : ℕ) (K : Window E a b) :
    ((originalProjectionStep E a b n).app K).hom = (projection E a b n K).hom := rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n : ℕ`, and `K : Window E
a b`,
`((originalProjectionStep E a b n).app K).hom.hom = (projection E a b n K).hom.hom`.
The raw cochain map is the chosen projection at the current cutoff `b−n`. -/
theorem originalProjectionStep_app_raw (a b : ℤ) (n : ℕ) (K : Window E a b) :
    ((originalProjectionStep E a b n).app K).hom.hom = (projection E a b n K).hom.hom := rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts and `a,b : ℤ`,
`originalProjection E a b n : 𝟭 (Window E a b) ⟶ originalFunctor E a b n` composes the
selected top-quotient projections in their iteration order. It starts with the identity
comparison at `n=0` and appends `originalProjectionStep E a b n` at each successor. -/
def originalProjection (a b : ℤ) : (n : ℕ) → 𝟭 (Window E a b) ⟶ originalFunctor E a b n :=
  Nat.rec (eqToHom (originalFunctor_zero E a b).symm)
    (fun n α => α ≫ originalProjectionStep E a b n)

/-- For a preadditive exact category `E` with a zero object and binary biproducts and `a,b : ℤ`,
`originalProjection E a b 0 = eqToHom (originalFunctor_zero E a b).symm`.
This is the natural comparison from the identity functor to the equal zero-step quotient functor. -/
theorem originalProjection_zero (a b : ℤ) :
    originalProjection E a b 0 = eqToHom (originalFunctor_zero E a b).symm := rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and `n : ℕ`,
`originalProjection E a b (n+1) = originalProjection E a b n ≫ originalProjectionStep E a b n`.
The next selected quotient projection is appended after the existing `n`-step projection. -/
theorem originalProjection_succ (a b : ℤ) (n : ℕ) :
    originalProjection E a b (n + 1) =
      originalProjection E a b n ≫ originalProjectionStep E a b n := rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n : ℕ`, `K : Window E a
b`, and `j : ℤ`,
`((originalProjection E a b (n+1)).app K).hom.hom.f j = ((originalProjection E a b n).app K).hom.hom.f j ≫ (projection E
a b n K).hom.hom.f j`.
The order is the projection to stage `n`, followed by that stage's quotient projection. -/
theorem originalProjection_succ_f (a b : ℤ) (n : ℕ) (K : Window E a b) (j : ℤ) :
    ((originalProjection E a b (n + 1)).app K).hom.hom.f j =
      ((originalProjection E a b n).app K).hom.hom.f j ≫ (projection E a b n K).hom.hom.f j :=
  rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n : ℕ`, `f : K ⟶ L` in
`Window E a b`, and `j : ℤ`, let `π_n=originalProjection E a b n` and `Q_n=originalFunctor E a b n`. Then
`(π_n.app K).hom.hom.f j ≫ (Q_n.map f).hom.hom.f j = f.hom.hom.f j ≫ (π_n.app L).hom.hom.f j`.
Both maps go from `K`'s degree-`j` term to the iterated quotient of `L` in degree `j`. -/
theorem originalProjection_naturality_f (a b : ℤ) (n : ℕ)
    {K L : Window E a b} (f : K ⟶ L) (j : ℤ) :
    ((originalProjection E a b n).app K).hom.hom.f j ≫
        ((originalFunctor E a b n).map f).hom.hom.f j =
      f.hom.hom.f j ≫ ((originalProjection E a b n).app L).hom.hom.f j :=
  congrArg (fun g => g.hom.hom.f j) ((originalProjection E a b n).naturality f).symm

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n : ℕ`, `K : Window E a
b`, and `j : ℤ` with `j≤cutoff b n`, the component
`((originalProjection E a b n).app K).hom.hom.f j`
is an isomorphism. Removing the first `n` top degrees retains every degree at or below `b−n` up to this projection
isomorphism. -/
theorem originalProjection_isIso_f (a b : ℤ) :
    ∀ (n : ℕ) (K : Window E a b) (j : ℤ), j ≤ cutoff b n →
      IsIso (((originalProjection E a b n).app K).hom.hom.f j) := by
  intro n
  induction n with
  | zero =>
    intro K j _hj
    change IsIso (𝟙 (K.obj.obj.X j))
    infer_instance
  | succ n ih =>
    intro K j hj
    have hjn : j ≤ cutoff b n := by
      rw [cutoff_eq] at hj ⊢
      omega
    have hjne : j ≠ cutoff b n := by
      rw [cutoff_eq] at hj ⊢
      omega
    rw [originalProjection_succ_f]
    exact IsIso.comp_isIso' (ih K j hjn)
      (windowTopQuotientProjection_isIso_f E a (cutoff b n) ((functor E a b n).obj K) j hjne)

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n : ℕ`, `j≤cutoff b n`,
and `K : Window E a b`, there is an isomorphism
`(windowEval E a b j).obj K ≅ (windowEval E a b j).obj ((originalFunctor E a b n).obj K)`.
Its forward map is the degree-`j` component of the composed quotient projection. -/
@[implicit_reducible]
def originalProjectionEvalComponentIso (a b : ℤ) (n : ℕ) (j : ℤ)
    (hj : j ≤ cutoff b n) (K : Window E a b) :
    (windowEval E a b j).obj K ≅
      (windowEval E a b j).obj ((originalFunctor E a b n).obj K) := by
  exact @asIso E _ _ _ (((originalProjection E a b n).app K).hom.hom.f j)
    (originalProjection_isIso_f E a b n K j hj)

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n : ℕ`, and `j : ℤ` with
`j≤cutoff b n`, the projection components give a natural isomorphism
`windowEval E a b j ≅ originalFunctor E a b n ⋙ windowEval E a b j`.
It compares each input term in degree `j` with that degree of its iterated quotient. -/
def originalProjectionEvalIso (a b : ℤ) (n : ℕ) (j : ℤ) (hj : j ≤ cutoff b n) :
    windowEval E a b j ≅ originalFunctor E a b n ⋙ windowEval E a b j :=
  NatIso.ofComponents (originalProjectionEvalComponentIso E a b n j hj) (by
    intro K L f
    change f.hom.hom.f j ≫ ((originalProjection E a b n).app L).hom.hom.f j =
      ((originalProjection E a b n).app K).hom.hom.f j ≫
        ((originalFunctor E a b n).map f).hom.hom.f j
    exact (originalProjection_naturality_f E a b n f j).symm)

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n : ℕ`, `j≤cutoff b n`,
and `K : Window E a b`,
`(originalProjectionEvalIso E a b n j hj).hom.app K = ((originalProjection E a b n).app K).hom.hom.f j`.
The natural term comparison uses the composed quotient-projection component. -/
theorem originalProjectionEvalIso_hom_app (a b : ℤ) (n : ℕ) (j : ℤ)
    (hj : j ≤ cutoff b n) (K : Window E a b) :
    (originalProjectionEvalIso E a b n j hj).hom.app K =
      ((originalProjection E a b n).app K).hom.hom.f j := rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n : ℕ`, `j≤cutoff b n`,
and `K : Window E a b`,
`(originalProjectionEvalIso E a b n j hj).inv.app K = inv (((originalProjection E a b n).app K).hom.hom.f j)`.
The bound on `j` supplies the isomorphism whose inverse is used. -/
theorem originalProjectionEvalIso_inv_app (a b : ℤ) (n : ℕ) (j : ℤ)
    (hj : j ≤ cutoff b n) (K : Window E a b) :
    letI := originalProjection_isIso_f E a b n K j hj
    (originalProjectionEvalIso E a b n j hj).inv.app K =
      inv (((originalProjection E a b n).app K).hom.hom.f j) := rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and `K : Window E a b`,
`IsZero ((originalFunctor E a b (length a b)).obj K)`.
After `length a b=(b−a+1).toNat` quotients, the cutoff lies below `a`; inclusion of that reversed-window zero object
into the input window preserves its zero property. -/
theorem original_terminal_isZero (a b : ℤ) (K : Window E a b) :
    IsZero ((originalFunctor E a b (length a b)).obj K) :=
  (includeOriginal_isWaldhausenExact E a b (length a b)).map_isZero (terminal_isZero E a b K)

/-- For `a,b : ℤ`, `n : ℕ`, and `hn : n<length a b`,
`cutoff b n = windowGradedDegree a b ⟨n,hn⟩`.
Both are the descending integer degree `b−n` in the fixed window. -/
theorem cutoff_eq_gradedDegree (a b : ℤ) (n : ℕ) (hn : n < length a b) :
    cutoff b n = windowGradedDegree a b ⟨n, hn⟩ := by
  rw [cutoff_eq]
  rfl

/-- For `a,b : ℤ`, `n : ℕ`, and `n<length a b=(b−a+1).toNat`,
`a≤cutoff b n ∧ cutoff b n≤b`.
The supporting degree `b−n` of a nonterminal quotient step lies in `[a,b]`. -/
theorem cutoff_mem (a b : ℤ) (n : ℕ) (hn : n < length a b) :
    a ≤ cutoff b n ∧ cutoff b n ≤ b := by
  rw [cutoff_eq_gradedDegree a b n hn]
  exact windowGradedDegree_mem a b ⟨n, hn⟩

/-- For a preadditive category `E` with a zero object, `a,b : ℤ`, `n : ℕ`, and `hn : n<length a
b`, the functor `originalSupportedSingle E a b n hn : E ⥤ Window E a b` places an object in
degree `cutoff b n=b−n`. The inequalities `a≤cutoff b n≤b` supply the window-support witness. -/
def originalSupportedSingle (a b : ℤ) (n : ℕ) (hn : n < length a b) : E ⥤ Window E a b :=
  windowSingle E a b (cutoff b n) (cutoff_mem a b n hn).1 (cutoff_mem a b n hn).2

omit [HasBinaryBiproducts E] [ExactCategory E] in
/-- For a preadditive category `E` with a zero object, `a,b : ℤ`, `n : ℕ`, and `hn : n<length a b`,
`originalSupportedSingle E a b n hn = windowGradedSingle E a b ⟨n,hn⟩`.
The cutoff and graded-coordinate constructions give the same supported single functor in degree `b−n`. -/
theorem originalSupportedSingle_eq (a b : ℤ) (n : ℕ) (hn : n < length a b) :
    originalSupportedSingle E a b n hn = windowGradedSingle E a b ⟨n, hn⟩ := by
  simp only [originalSupportedSingle, windowGradedSingle, cutoff_eq, windowGradedDegree]

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and
`n : ℕ`, the endofunctor `originalTopFunctor E a b n` first performs `n` top quotients, then
extracts the single of its top term in degree `cutoff b n`, and includes that single into
`Window E a b`. It is `functor E a b n ⋙ windowTopSingleFunctor E a (cutoff b n) ⋙
includeOriginal E a b n`. -/
def originalTopFunctor (a b : ℤ) (n : ℕ) : Window E a b ⥤ Window E a b :=
  functor E a b n ⋙ windowTopSingleFunctor E a (cutoff b n) ⋙ includeOriginal E a b n

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b,j : ℤ`, and `n : ℕ`,
`originalFunctor E a b n ⋙ windowEval E a b j = functor E a b n ⋙ windowEval E a (cutoff b n) j`.
The two evaluation functors return the same cochain term of the iterated quotient. -/
theorem originalFunctor_comp_eval (a b : ℤ) (n : ℕ) (j : ℤ) :
    originalFunctor E a b n ⋙ windowEval E a b j =
      functor E a b n ⋙ windowEval E a (cutoff b n) j := rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n : ℕ`, and `hn :
n<length a b`,
`originalTopFunctor E a b n = originalFunctor E a b n ⋙ windowEval E a b (cutoff b n) ⋙ originalSupportedSingle E a b n
hn`.
The top term of the iterated quotient is placed in its supported single at the cutoff. -/
theorem originalTopFunctor_eq_eval_single (a b : ℤ) (n : ℕ) (hn : n < length a b) :
    originalTopFunctor E a b n =
      originalFunctor E a b n ⋙ windowEval E a b (cutoff b n) ⋙
        originalSupportedSingle E a b n hn := rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and `n<length a b`, there
is a natural isomorphism
`windowEval E a b (cutoff b n) ⋙ originalSupportedSingle E a b n hn ≅ originalTopFunctor E a b n`.
It applies the supported single functor to the projection isomorphism between the input cutoff term and the same term of
its iterated quotient. -/
def originalTopFunctorIso (a b : ℤ) (n : ℕ) (hn : n < length a b) :
    windowEval E a b (cutoff b n) ⋙ originalSupportedSingle E a b n hn ≅
      originalTopFunctor E a b n :=
  Functor.isoWhiskerRight (originalProjectionEvalIso E a b n (cutoff b n) le_rfl)
    (originalSupportedSingle E a b n hn)

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n<length a b`, and
`i=⟨n,hn⟩`, there is a natural isomorphism
`windowEval E a b (windowGradedDegree a b i) ⋙ windowGradedSingle E a b i ≅ originalTopFunctor E a b n`.
It uses `cutoff b n=windowGradedDegree a b i` and the equality of the cutoff and graded single embeddings. -/
def originalGradedTopFunctorIso (a b : ℤ) (n : ℕ) (hn : n < length a b) :
    windowEval E a b (windowGradedDegree a b ⟨n, hn⟩) ⋙ windowGradedSingle E a b ⟨n, hn⟩ ≅
      originalTopFunctor E a b n :=
  eqToIso (by rw [← cutoff_eq_gradedDegree a b n hn, ← originalSupportedSingle_eq E a b n hn]) ≪≫
    originalTopFunctorIso E a b n hn

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n<length a b`, and `K :
Window E a b`,
`((originalTopFunctorIso E a b n hn).hom.app K).hom = (single E (cutoff b n)).map (((originalProjection E a b n).app
K).hom.hom.f (cutoff b n))`.
The bounded chart is the single-degree image of the cutoff projection component. -/
theorem originalTopFunctorIso_hom_app_hom (a b : ℤ) (n : ℕ) (hn : n < length a b)
    (K : Window E a b) :
    ((originalTopFunctorIso E a b n hn).hom.app K).hom =
      (single E (cutoff b n)).map (((originalProjection E a b n).app K).hom.hom.f (cutoff b n)) :=
  rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n<length a b`, and `K :
Window E a b`, the raw forward chart is
`(HomologicalComplex.single E (.up ℤ) (cutoff b n)).map (((originalProjection E a b n).app K).hom.hom.f (cutoff b n))`.
This equals `((originalTopFunctorIso E a b n hn).hom.app K).hom.hom`. -/
theorem originalTopFunctorIso_hom_app_raw (a b : ℤ) (n : ℕ) (hn : n < length a b)
    (K : Window E a b) :
    ((originalTopFunctorIso E a b n hn).hom.app K).hom.hom =
      (HomologicalComplex.single E (.up ℤ) (cutoff b n)).map
        (((originalProjection E a b n).app K).hom.hom.f (cutoff b n)) := rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n<length a b`, and `K :
Window E a b`,
`((originalTopFunctorIso E a b n hn).inv.app K).hom = (single E (cutoff b n)).map (originalProjectionEvalComponentIso E
a b n (cutoff b n) le_rfl K).inv`.
The inverse chart is the single-degree image of the inverse cutoff projection isomorphism. -/
theorem originalTopFunctorIso_inv_app_hom (a b : ℤ) (n : ℕ) (hn : n < length a b)
    (K : Window E a b) :
    ((originalTopFunctorIso E a b n hn).inv.app K).hom =
      (single E (cutoff b n)).map
        (originalProjectionEvalComponentIso E a b n (cutoff b n) le_rfl K).inv := rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `n<length a b`, and `K :
Window E a b`, the raw inverse chart is
`(HomologicalComplex.single E (.up ℤ) (cutoff b n)).map (originalProjectionEvalComponentIso E a b n (cutoff b n) le_rfl
K).inv`.
This equals `((originalTopFunctorIso E a b n hn).inv.app K).hom.hom`. -/
theorem originalTopFunctorIso_inv_app_raw (a b : ℤ) (n : ℕ) (hn : n < length a b)
    (K : Window E a b) :
    ((originalTopFunctorIso E a b n hn).inv.app K).hom.hom =
      (HomologicalComplex.single E (.up ℤ) (cutoff b n)).map
        (originalProjectionEvalComponentIso E a b n (cutoff b n) le_rfl K).inv := rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and
`n : ℕ`, `originalTopInclusion E a b n : originalTopFunctor E a b n ⟶ originalFunctor E a b n`
is the top-single inclusion at cutoff `b−n`, precomposed with the quotient iteration and then
included in the input window. -/
def originalTopInclusion (a b : ℤ) (n : ℕ) :
    originalTopFunctor E a b n ⟶ originalFunctor E a b n :=
  Functor.whiskerRight
    (Functor.whiskerLeft (functor E a b n) (windowTopInclusion E a (cutoff b n)))
    (includeOriginal E a b n)

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and
`n : ℕ`, the exact endofunctors `Top_n=originalTopFunctor E a b n`, `Q_n=originalFunctor E a b
n`, and `Q_{n+1}` form a Waldhausen cofiber functor sequence with arrows `originalTopInclusion
E a b n` and `originalProjectionStep E a b n`. Their object components are cofiber sequences.
For a source cofibration `f:X→Y`, the induced relative corner `Q_n(X) ⊔_{Top_n(X)} Top_n(Y) →
Q_n(Y)` is a cofibration. -/
theorem originalCofiberFunctorSequence (a b : ℤ) (n : ℕ) :
    IsWaldhausenCofiberFunctorSequence (originalTopFunctor E a b n) (originalFunctor E a b n)
      (originalFunctor E a b (n + 1)) (originalTopInclusion E a b n)
      (originalProjectionStep E a b n) :=
  ((windowTopCofiberFunctorSequence E a (cutoff b n)).precomp (functor E a b n)
    (functor_isWaldhausenExact E a b n)).postcomp (includeOriginal_isWaldhausenExact E a b n)

end CochainComplex.Bounded.WindowTopIteration

end
