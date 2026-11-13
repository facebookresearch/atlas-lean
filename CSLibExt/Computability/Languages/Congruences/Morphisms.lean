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

public import CSLibExt.Computability.Languages.Congruences.Regularity

/-!
# Syntactic monoids under alphabet morphisms

The inverse image of a language under a map of alphabets is recognized by composing its
syntactic morphism with the induced free-monoid morphism.  This gives both a direct syntactic
relation theorem and closure of finite syntactic monoids, hence regular languages, under alphabet
preimages.  Alphabet equivalences yield sharper transport results.
-/

@[expose] public section

open scoped Computability

namespace Cslib.Language

universe u v

variable {Source : Type u} {Target : Type v}

/-- **Alphabet preimage.** Let $f \colon \Sigma \to \Gamma$ be a map between alphabets and $L$ a
language over $\Gamma$. The alphabet preimage of $L$ under $f$ is the language over $\Sigma$
consisting of the words $a_1 a_2 \cdots a_n$ such that $f(a_1) f(a_2) \cdots f(a_n) \in L$. -/
def alphabetPreimage (f : Source → Target) (L : Language Target) : Language Source :=
  {x | x.map f ∈ L}

@[simp]
theorem mem_alphabetPreimage_iff (f : Source → Target) (L : Language Target)
    (x : List Source) : x ∈ alphabetPreimage f L ↔ x.map f ∈ L :=
  Iff.rfl

@[simp]
theorem alphabetPreimage_id (L : Language Source) : alphabetPreimage id L = L := by
  ext x
  change x.map id ∈ L ↔ x ∈ L
  rw [List.map_id]

theorem alphabetPreimage_comp {Third : Type*} (g : Target → Third) (f : Source → Target)
    (L : Language Third) :
    alphabetPreimage f (alphabetPreimage g L) = alphabetPreimage (g ∘ f) L := by
  ext x
  change (x.map f).map g ∈ L ↔ x.map (g ∘ f) ∈ L
  rw [List.map_map]

/-- **Alphabet preimage morphism.** Let $f \colon \Sigma \to \Gamma$ be a map between alphabets
and $L$ a language over $\Gamma$. The alphabet preimage morphism of $f$ and $L$ is the monoid
morphism from the free monoid $\Sigma^*$ to the syntactic monoid of $L$ that sends a word $w$ to
the syntactic class of $f^*(w)$, the word obtained by applying $f$ to each letter of $w$. It is
the composite of the letterwise map $f^* \colon \Sigma^* \to \Gamma^*$ with the syntactic
morphism of $L$. -/
def alphabetPreimageMorphism (f : Source → Target) (L : Language Target) :
    FreeMonoid Source →* SyntacticMonoid L :=
  (syntacticMorphism L).comp (FreeMonoid.map f)

@[simp]
theorem alphabetPreimageMorphism_apply (f : Source → Target) (L : Language Target)
    (x : FreeMonoid Source) :
    alphabetPreimageMorphism f L x = syntacticMorphism L (FreeMonoid.map f x) :=
  rfl

/-- **The alphabet preimage morphism recognizes the alphabet preimage.** Let
$f \colon \Sigma \to \Gamma$ be a map between alphabets and $L$ a language over $\Gamma$. Write
$f^*(w)$ for the word obtained by applying $f$ to each letter of a word $w$, $[u]_L$ for the
class of a word $u$ in the syntactic monoid $M(L)$ of $L$, $A_L \subseteq M(L)$ for the
accepting set of classes of words in $L$, and $\varphi \colon \Sigma^* \to M(L)$ for the alphabet
preimage morphism $w \mapsto [f^*(w)]_L$. Then $\varphi$ recognizes the alphabet preimage
$\{w \in \Sigma^* \mid f^*(w) \in L\}$ through $A_L$: for every word $w \in \Sigma^*$, we have
$f^*(w) \in L$ if and only if $\varphi(w) \in A_L$. -/
theorem recognizes_alphabetPreimageMorphism (f : Source → Target) (L : Language Target) :
    Recognizes (alphabetPreimage f L) (alphabetPreimageMorphism f L) (syntacticAccept L) := by
  intro x
  change (FreeMonoid.toList x).map f ∈ L ↔
    syntacticMorphism L (FreeMonoid.map f x) ∈ syntacticAccept L
  exact syntacticMorphism_mem_accept L (FreeMonoid.map f x)

/-- **Syntactic equivalence pulls back along an alphabet map.** Let $f \colon \Sigma \to \Gamma$
be a map between alphabets, $L$ a language over $\Gamma$, and $K$ the alphabet preimage
$\{w \in \Sigma^* \mid f^*(w) \in L\}$, where $f^*(w)$ is the word obtained by applying $f$ to
each letter of $w$. If $x, y \in \Sigma^*$ are words such that $f^*(x)$ and $f^*(y)$ are
syntactically equivalent for $L$, then $x$ and $y$ are syntactically equivalent for $K$. -/
theorem syntacticRel_alphabetPreimage_of_map (f : Source → Target) (L : Language Target)
    {x y : FreeMonoid Source} (h : syntacticRel L (FreeMonoid.map f x) (FreeMonoid.map f y)) :
    syntacticRel (alphabetPreimage f L) x y := by
  intro u v
  change (FreeMonoid.toList (u * x * v)).map f ∈ L ↔
    (FreeMonoid.toList (u * y * v)).map f ∈ L
  simpa only [← FreeMonoid.toList_map, map_mul] using
    h (FreeMonoid.map f u) (FreeMonoid.map f v)

/-- **The alphabet preimage morphism refines the preimage's syntactic congruence.** Let
$f \colon \Sigma \to \Gamma$ be a map between alphabets, $L$ a language over $\Gamma$ with
syntactic monoid $M(L)$, and $\varphi \colon \Sigma^* \to M(L)$ the alphabet preimage morphism,
which sends a word $w$ to the class in $M(L)$ of the word $f^*(w)$ obtained by applying $f$ to
each letter of $w$. If two words $x, y \in \Sigma^*$ satisfy $\varphi(x) = \varphi(y)$, then $x$
and $y$ are syntactically congruent for the alphabet preimage
$\{w \in \Sigma^* \mid f^*(w) \in L\}$. In other words, the kernel congruence of $\varphi$ is
contained in the syntactic congruence of the alphabet preimage. -/
theorem alphabetPreimageMorphism_ker_le (f : Source → Target) (L : Language Target) :
    Con.ker (alphabetPreimageMorphism f L) ≤ syntacticCon (alphabetPreimage f L) :=
  recognizer_ker_le_syntacticCon (recognizes_alphabetPreimageMorphism f L)

/-- **Division map for the syntactic monoid of an alphabet preimage.** Let
$f \colon \Sigma \to \Gamma$ be a map between alphabets and $L$ a language over $\Gamma$. Write
$f^*(w)$ for the word obtained by applying $f$ to each letter of a word $w$, $[u]_L$ for the
class of a word $u$ in the syntactic monoid $M(L)$ of $L$, $K$ for the alphabet preimage
$\{w \in \Sigma^* \mid f^*(w) \in L\}$, and $\varphi \colon \Sigma^* \to M(L)$ for the alphabet
preimage morphism $w \mapsto [f^*(w)]_L$. This is the monoid morphism from the submonoid
$\varphi(\Sigma^*)$ of $M(L)$ to the syntactic monoid $M(K)$ that sends $\varphi(w)$ to $[w]_K$;
it is well defined because $\varphi(x) = \varphi(y)$ implies $[x]_K = [y]_K$.

This morphism is surjective, so $M(K)$ is a quotient of a submonoid of $M(L)$. -/
noncomputable def alphabetPreimageToSyntactic (f : Source → Target) (L : Language Target) :
    MonoidHom.mrange (alphabetPreimageMorphism f L) →*
      SyntacticMonoid (alphabetPreimage f L) :=
  recognizerImageToSyntactic (alphabetPreimageMorphism f L) (syntacticAccept L)
    (recognizes_alphabetPreimageMorphism f L)

theorem alphabetPreimageToSyntactic_surjective (f : Source → Target)
    (L : Language Target) : Function.Surjective (alphabetPreimageToSyntactic f L) :=
  recognizerImageToSyntactic_surjective (alphabetPreimageMorphism f L) (syntacticAccept L)
    (recognizes_alphabetPreimageMorphism f L)

/-- **Alphabet preimages preserve finiteness of the syntactic monoid.** Let
$f \colon \Sigma \to \Gamma$ be a map between alphabets and $L$ a language over $\Gamma$ whose
syntactic monoid is finite. Then the syntactic monoid of the alphabet preimage
$\{w \in \Sigma^* \mid f^*(w) \in L\}$ is finite, where $f^*(w)$ is the word obtained by applying
$f$ to each letter of $w$. -/
theorem finite_syntacticMonoid_alphabetPreimage (f : Source → Target) (L : Language Target)
    [Finite (SyntacticMonoid L)] : Finite (SyntacticMonoid (alphabetPreimage f L)) :=
  finite_syntacticMonoid_of_recognizer (alphabetPreimageMorphism f L) (syntacticAccept L)
    (recognizes_alphabetPreimageMorphism f L)

/-- **Regular languages are closed under alphabet preimages.** Let $f \colon \Sigma \to \Gamma$
be a map between alphabets. If $L$ is a regular language over $\Gamma$, then its alphabet
preimage $\{w \in \Sigma^* \mid f^*(w) \in L\}$ is regular, where $f^*(w)$ is the word obtained
by applying $f$ to each letter of $w$. -/
theorem IsRegular.alphabetPreimage {L : Language Target} (hL : L.IsRegular)
    (f : Source → Target) : (alphabetPreimage f L).IsRegular := by
  rw [Cslib.Language.isRegular_iff_finite_syntacticMonoid] at hL ⊢
  let _ : Finite (SyntacticMonoid L) := hL
  exact finite_syntacticMonoid_alphabetPreimage f L

/-- **Renaming letters by a bijection preserves and reflects regularity.** Let
$e \colon \Sigma \to \Gamma$ be a bijection between alphabets and $L$ a language over $\Gamma$.
The alphabet preimage $\{w \in \Sigma^* \mid e^*(w) \in L\}$, where $e^*(w)$ is the word
obtained by applying $e$ to each letter of $w$, is regular if and only if $L$ is regular. -/
theorem isRegular_alphabetPreimage_equiv_iff (e : Source ≃ Target) (L : Language Target) :
    (alphabetPreimage e L).IsRegular ↔ L.IsRegular := by
  constructor
  · intro h
    have hpre := Cslib.Language.IsRegular.alphabetPreimage h e.symm
    rw [alphabetPreimage_comp] at hpre
    have he : e ∘ e.symm = id := funext e.apply_symm_apply
    rw [he, alphabetPreimage_id] at hpre
    exact hpre
  · intro h
    exact Cslib.Language.IsRegular.alphabetPreimage h e

/-- **Finiteness of the syntactic monoid is invariant under renaming letters.** Let
$e \colon \Sigma \to \Gamma$ be a bijection between alphabets and $L$ a language over $\Gamma$.
The syntactic monoid of the alphabet preimage $\{w \in \Sigma^* \mid e^*(w) \in L\}$, where
$e^*(w)$ is the word obtained by applying $e$ to each letter of $w$, is finite if and only if
the syntactic monoid of $L$ is finite. -/
theorem finite_syntacticMonoid_alphabetPreimage_equiv_iff (e : Source ≃ Target)
    (L : Language Target) :
    Finite (SyntacticMonoid (alphabetPreimage e L)) ↔ Finite (SyntacticMonoid L) := by
  rw [← isRegular_iff_finite_syntacticMonoid,
    ← isRegular_iff_finite_syntacticMonoid]
  exact isRegular_alphabetPreimage_equiv_iff e L

end Cslib.Language
