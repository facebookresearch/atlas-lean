/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-! # Algebraic matroids

Following Matt Larson and Tuong Le, _Duals of algebraic matroids need not
be algebraic_ (arXiv:2609.02834v1), Introduction lines 57-59: a matroid is
algebraic if its independent sets are the algebraically independent subsets
of a field extension under a realization of the ground set.
-/

universe u v w

@[expose] public section

namespace Matroid

/-- **Algebraic representation of a matroid.** Let $K$ be a field and $M$ a matroid on a type $E$.
An algebraic representation of $M$ over $K$ consists of a field extension $L$ of $K$ and a map
$\varphi \colon E \to L$ such that $L$ is generated over $K$ by the image under $\varphi$ of the
ground set of $M$, and a set $I$ is independent in $M$ exactly when $I$ is contained in the ground
set of $M$, $\varphi$ is injective on $I$, and $\varphi(I)$ is algebraically independent over
$K$. -/
structure AlgebraicRepresentation (K : Type u) [Field K] {E : Type v}
    (M : Matroid E) where
  /-- Ambient extension field holding the realization. -/
  L : Type w
  /-- Field structure on the ambient extension. -/
  [field : Field L]
  /-- `K`-algebra structure on the ambient extension. -/
  [algebra : Algebra K L]
  /-- Faithfulness of the scalar action of `K` on `L`. -/
  [faithful : FaithfulSMul K L]
  /-- Map sending each ground-set element to `L`. -/
  realize : E → L
  /-- The realized ground set generates `L` over `K`. -/
  generates : IntermediateField.adjoin K (realize '' M.E) = ⊤
  /-- Independence in `M` matches algebraic independence in `L`. -/
  matroid_eq : M = (AlgebraicIndependent.matroid K L).comapOn M.E realize

attribute [instance] AlgebraicRepresentation.field AlgebraicRepresentation.algebra
  AlgebraicRepresentation.faithful

/-- **Algebraic matroid over a field.** Let $K$ be a field. A matroid $M$ on a type $E$ is
algebraic over $K$ if it has an algebraic representation over $K$ whose extension field lies in
the larger of the universes of $K$ and $E$.

Universe encoding: Lean fixes universes, so the witness extension is required to live in a
universe holding both $K$ and $E$. -/
def IsAlgebraicOver (K : Type u) [Field K] {E : Type v}
    (M : Matroid E) : Prop :=
  Nonempty (AlgebraicRepresentation.{u, v, max u v} K M)

/-- **Algebraic representation of a matroid over some field.** Let $M$ be a matroid on a type
$E$. An algebraic representation of $M$ over some field consists of a field $K$, a field extension
$L$ of $K$ and a map $\varphi \colon E \to L$ such that $L$ is generated over $K$ by the image
under $\varphi$ of the ground set of $M$, and a set $I$ is independent in $M$ exactly when $I$ is
contained in the ground set of $M$, $\varphi$ is injective on $I$, and $\varphi(I)$ is
algebraically independent over $K$.

Universe encoding: both $K$ and $L$ lie in the same universe as $E$, so matroids on $E$ need no
larger universes. -/
structure AlgebraicRepresentationSomeField {E : Type v}
    (M : Matroid E) where
  /-- Base field of the realization, in the same universe as `E`. -/
  K : Type v
  /-- Field structure on the base field. -/
  [fieldK : Field K]
  /-- Extension field holding the realization. -/
  L : Type v
  /-- Field structure on the extension. -/
  [fieldL : Field L]
  /-- `K`-algebra structure on the extension. -/
  [algebra : Algebra K L]
  /-- Faithfulness of the scalar action of `K` on `L`. -/
  [faithful : FaithfulSMul K L]
  /-- Map sending each ground-set element to `L`. -/
  realize : E → L
  /-- The realized ground set generates `L` over `K`. -/
  generates : IntermediateField.adjoin K (realize '' M.E) = ⊤
  /-- Independence in `M` matches algebraic independence in `L`. -/
  matroid_eq : M = (AlgebraicIndependent.matroid K L).comapOn M.E realize

attribute [instance] AlgebraicRepresentationSomeField.fieldK
  AlgebraicRepresentationSomeField.fieldL AlgebraicRepresentationSomeField.algebra
  AlgebraicRepresentationSomeField.faithful

/-- **Algebraic matroid.** A matroid $M$ on a type $E$ is algebraic if it has an algebraic
representation over some field whose base field and extension field lie in the same universe
as $E$.

Universe encoding: this is the universe-local form of algebraicity for matroids on $E$. -/
def IsAlgebraic {E : Type v} (M : Matroid E) : Prop :=
  Nonempty (AlgebraicRepresentationSomeField M)

/-- **Algebraic representations witness algebraicity over a field.** Let $K$ be a field and $M$
a matroid on a type $E$. If $M$ has an algebraic representation over $K$ whose extension field
lies in the larger of the universes of $K$ and $E$, then $M$ is algebraic over $K$. -/
theorem AlgebraicRepresentation.toIsAlgebraicOver {K : Type u} [Field K]
    {E : Type v} {M : Matroid E}
    (self : AlgebraicRepresentation.{u, v, max u v} K M) :
    IsAlgebraicOver K M :=
  ⟨self⟩

/-- **Representations over some field witness algebraicity.** If a matroid $M$ on a type $E$
has an algebraic representation over some field whose base field and extension field lie in the
same universe as $E$, then $M$ is algebraic. -/
theorem AlgebraicRepresentationSomeField.toIsAlgebraic {E : Type v}
    {M : Matroid E} (self : AlgebraicRepresentationSomeField M) :
    IsAlgebraic M :=
  ⟨self⟩

end Matroid
