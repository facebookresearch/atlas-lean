/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `290c48922e071d1e4267dd103a14e73b547adf60`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import CSLibExt.Computability.Languages.Congruences.Morphisms

/-!
# Inverse images under free-monoid morphisms

Alphabet maps are a special case of substitutions that send each source letter to an arbitrary
target word.  Such substitutions are precisely monoid morphisms between free monoids.  Composing
a recognizer with a substitution recognizes the inverse-image language, proving closure of finite
syntactic monoids and regular languages under inverse morphisms.
-/

@[expose] public section

open scoped Computability

namespace Cslib.Language

universe u v w

variable {Source : Type u} {Target : Type v}

/-- **Inverse image under a word morphism.** Let $\Sigma$ and $\Gamma$ be alphabets,
$h \colon \Sigma^* \to \Gamma^*$ a monoid morphism between their free monoids of words, and $L$ a
language over $\Gamma$. The inverse image of $L$ under $h$ is the language
$h^{-1}(L) = \{w \in \Sigma^* \mid h(w) \in L\}$ over $\Sigma$. -/
def wordMorphismPreimage (substitution : FreeMonoid Source →* FreeMonoid Target)
    (L : Language Target) : Language Source :=
  {x | FreeMonoid.toList (substitution (FreeMonoid.ofList x)) ∈ L}

@[simp]
theorem mem_wordMorphismPreimage_iff
    (substitution : FreeMonoid Source →* FreeMonoid Target) (L : Language Target)
    (x : List Source) :
    x ∈ wordMorphismPreimage substitution L ↔
      FreeMonoid.toList (substitution (FreeMonoid.ofList x)) ∈ L :=
  Iff.rfl

@[simp]
theorem wordMorphismPreimage_id (L : Language Source) :
    wordMorphismPreimage (MonoidHom.id (FreeMonoid Source)) L = L := by
  ext x
  change FreeMonoid.toList (FreeMonoid.ofList x) ∈ L ↔ x ∈ L
  rfl

/-- **Word morphisms act letter by letter.** Let $h \colon \Sigma^* \to \Gamma^*$ be a monoid
morphism between free monoids. For every word $a_1 a_2 \cdots a_n \in \Sigma^*$ (including the
empty word, $n = 0$), we have $h(a_1 a_2 \cdots a_n) = h(a_1) h(a_2) \cdots h(a_n)$, the
concatenation of the images of its letters. -/
theorem toList_wordMorphism_ofList (substitution : FreeMonoid Source →* FreeMonoid Target)
    (x : List Source) :
    FreeMonoid.toList (substitution (FreeMonoid.ofList x)) =
      (x.map fun a => FreeMonoid.toList (substitution (FreeMonoid.of a))).flatten := by
  induction x with
  | nil => simp
  | cons a x ih =>
      rw [FreeMonoid.ofList_cons, map_mul, FreeMonoid.toList_mul, ih]
      rfl

/-- **Letterwise description of the inverse image under a word morphism.** Let
$h \colon \Sigma^* \to \Gamma^*$ be a monoid morphism between free monoids and $L$ a language over
$\Gamma$. The inverse image $h^{-1}(L) = \{w \in \Sigma^* \mid h(w) \in L\}$ consists exactly of
the words $a_1 a_2 \cdots a_n \in \Sigma^*$ such that the concatenation
$h(a_1) h(a_2) \cdots h(a_n)$ of the images of their letters lies in $L$. -/
theorem wordMorphismPreimage_eq_flatten (substitution : FreeMonoid Source →* FreeMonoid Target)
    (L : Language Target) :
    wordMorphismPreimage substitution L =
      {x | (x.map fun a => FreeMonoid.toList (substitution (FreeMonoid.of a))).flatten ∈ L} := by
  ext x
  rw [mem_wordMorphismPreimage_iff, toList_wordMorphism_ofList]
  rfl

theorem wordMorphismPreimage_comp {Third : Type w}
    (outer : FreeMonoid Target →* FreeMonoid Third)
    (inner : FreeMonoid Source →* FreeMonoid Target) (L : Language Third) :
    wordMorphismPreimage inner (wordMorphismPreimage outer L) =
      wordMorphismPreimage (outer.comp inner) L := by
  ext x
  change FreeMonoid.toList
      (outer (FreeMonoid.ofList (FreeMonoid.toList (inner (FreeMonoid.ofList x))))) ∈ L ↔
    FreeMonoid.toList (outer (inner (FreeMonoid.ofList x))) ∈ L
  rw [FreeMonoid.ofList_toList]

/-- **Recognizing morphism of an inverse image.** Let $h \colon \Sigma^* \to \Gamma^*$ be a monoid
morphism between free monoids and $L$ a language over $\Gamma$ with syntactic monoid $M(L)$. The
recognizing morphism of $h$ and $L$ is the monoid morphism $\Sigma^* \to M(L)$ that sends a word
$w$ to the syntactic class $[h(w)]_L$ of $h(w)$; it is the composite of $h$ with the syntactic
morphism of $L$. -/
def wordMorphismRecognizer (substitution : FreeMonoid Source →* FreeMonoid Target)
    (L : Language Target) : FreeMonoid Source →* SyntacticMonoid L :=
  (syntacticMorphism L).comp substitution

@[simp]
theorem wordMorphismRecognizer_apply
    (substitution : FreeMonoid Source →* FreeMonoid Target) (L : Language Target)
    (x : FreeMonoid Source) :
    wordMorphismRecognizer substitution L x = syntacticMorphism L (substitution x) :=
  rfl

theorem recognizes_wordMorphismRecognizer
    (substitution : FreeMonoid Source →* FreeMonoid Target) (L : Language Target) :
    Recognizes (wordMorphismPreimage substitution L) (wordMorphismRecognizer substitution L)
      (syntacticAccept L) := by
  intro x
  change FreeMonoid.toList (substitution x) ∈ L ↔
    syntacticMorphism L (substitution x) ∈ syntacticAccept L
  exact syntacticMorphism_mem_accept L (substitution x)

/-- **Syntactic equivalence pulls back along a word morphism.** Let
$h \colon \Sigma^* \to \Gamma^*$ be a monoid morphism between free monoids, $L$ a language over
$\Gamma$, and $K = h^{-1}(L) = \{w \in \Sigma^* \mid h(w) \in L\}$ its inverse image. If
$x, y \in \Sigma^*$ are words such that $h(x)$ and $h(y)$ are syntactically equivalent for $L$,
then $x$ and $y$ are syntactically equivalent for $K$. -/
theorem syntacticRel_wordMorphismPreimage_of_map
    (substitution : FreeMonoid Source →* FreeMonoid Target) (L : Language Target)
    {x y : FreeMonoid Source} (h : syntacticRel L (substitution x) (substitution y)) :
    syntacticRel (wordMorphismPreimage substitution L) x y := by
  intro p q
  change FreeMonoid.toList (substitution (p * x * q)) ∈ L ↔
    FreeMonoid.toList (substitution (p * y * q)) ∈ L
  simpa only [map_mul] using h (substitution p) (substitution q)

/-- **Division map for the syntactic monoid of an inverse image.** Let
$h \colon \Sigma^* \to \Gamma^*$ be a monoid morphism between free monoids and $L$ a language over
$\Gamma$. Write $[u]_L$ for the class of a word $u$ in the syntactic monoid $M(L)$ of $L$, $K$ for
the inverse image $h^{-1}(L) = \{w \in \Sigma^* \mid h(w) \in L\}$, and
$\varphi \colon \Sigma^* \to M(L)$ for the recognizing morphism $w \mapsto [h(w)]_L$. This is the
monoid morphism from the submonoid $\varphi(\Sigma^*)$ of $M(L)$ to the syntactic monoid $M(K)$
that sends $\varphi(w)$ to $[w]_K$; it is well defined because $\varphi(x) = \varphi(y)$ implies
$[x]_K = [y]_K$.

This morphism is surjective, so $M(K)$ is a quotient of a submonoid of $M(L)$. -/
noncomputable def wordMorphismPreimageToSyntactic
    (substitution : FreeMonoid Source →* FreeMonoid Target) (L : Language Target) :
    MonoidHom.mrange (wordMorphismRecognizer substitution L) →*
      SyntacticMonoid (wordMorphismPreimage substitution L) :=
  recognizerImageToSyntactic (wordMorphismRecognizer substitution L) (syntacticAccept L)
    (recognizes_wordMorphismRecognizer substitution L)

theorem wordMorphismPreimageToSyntactic_surjective
    (substitution : FreeMonoid Source →* FreeMonoid Target) (L : Language Target) :
    Function.Surjective (wordMorphismPreimageToSyntactic substitution L) :=
  recognizerImageToSyntactic_surjective (wordMorphismRecognizer substitution L)
    (syntacticAccept L) (recognizes_wordMorphismRecognizer substitution L)

/-- **Inverse images under word morphisms preserve finiteness of the syntactic monoid.** Let
$h \colon \Sigma^* \to \Gamma^*$ be a monoid morphism between free monoids and $L$ a language over
$\Gamma$ whose syntactic monoid is finite. Then the syntactic monoid of the inverse image
$h^{-1}(L) = \{w \in \Sigma^* \mid h(w) \in L\}$ is finite. -/
theorem finite_syntacticMonoid_wordMorphismPreimage
    (substitution : FreeMonoid Source →* FreeMonoid Target) (L : Language Target)
    [Finite (SyntacticMonoid L)] :
    Finite (SyntacticMonoid (wordMorphismPreimage substitution L)) :=
  finite_syntacticMonoid_of_recognizer (wordMorphismRecognizer substitution L)
    (syntacticAccept L) (recognizes_wordMorphismRecognizer substitution L)

/-- **Regular languages are closed under inverse word morphisms.** Let
$h \colon \Sigma^* \to \Gamma^*$ be a monoid morphism between free monoids. If $L$ is a regular
language over $\Gamma$, then its inverse image $h^{-1}(L) = \{w \in \Sigma^* \mid h(w) \in L\}$ is
regular. -/
theorem IsRegular.wordMorphismPreimage {L : Language Target} (hL : L.IsRegular)
    (substitution : FreeMonoid Source →* FreeMonoid Target) :
    (wordMorphismPreimage substitution L).IsRegular := by
  rw [Cslib.Language.isRegular_iff_finite_syntacticMonoid] at hL ⊢
  let _ : Finite (SyntacticMonoid L) := hL
  exact finite_syntacticMonoid_wordMorphismPreimage substitution L

/-- **Alphabet preimages are inverse images under word morphisms.** Let
$f \colon \Sigma \to \Gamma$ be a map between alphabets, $f^* \colon \Sigma^* \to \Gamma^*$ the
monoid morphism that applies $f$ to each letter of a word, and $L$ a language over $\Gamma$. Then
the alphabet preimage of $L$ under $f$ equals the inverse image
$(f^*)^{-1}(L) = \{w \in \Sigma^* \mid f^*(w) \in L\}$ of $L$ under $f^*$. -/
theorem alphabetPreimage_eq_wordMorphismPreimage (f : Source → Target)
    (L : Language Target) :
    alphabetPreimage f L = wordMorphismPreimage (FreeMonoid.map f) L := by
  ext x
  rfl

end Cslib.Language
