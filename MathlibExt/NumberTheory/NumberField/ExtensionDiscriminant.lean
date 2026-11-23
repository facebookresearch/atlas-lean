/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.LatticeDiscriminant

/-!
# Extension discriminants

For a tower A to B to L, imageOfB is the image of B in L as an A-submodule. The extension
discriminant is the lattice discriminant of that submodule.

The result is represented as an A-submodule of K, not literally as an Ideal A. Showing that it
comes from an integral ideal requires additional hypotheses.
-/

@[expose] public section

set_option autoImplicit false

universe u

section ImageOfB

variable (A : Type*) (L : Type u) (B : Type*)
  [CommRing A] [CommRing B] [Field L]
  [Algebra A B] [Algebra B L] [Algebra A L] [IsScalarTower A B L]

/-- **Image of $B$ in $L$.** Let $A$ and $B$ be commutative rings and $L$ a field, with algebra
maps $A \to B$, $B \to L$ and $A \to L$ forming a scalar tower. The image of $B$ in $L$ is the
range of the algebra map $B \to L$, regarded as an $A$-submodule of $L$. -/
def imageOfB : Submodule A L :=
  Subalgebra.toSubmodule (IsScalarTower.toAlgHom A B L).range

/-- **Membership in the image of $B$.** Let $A$ and $B$ be commutative rings and $L$ a field,
with algebra maps $A \to B$, $B \to L$ and $A \to L$ forming a scalar tower. An element
$x \in L$ lies in the image of $B$ in $L$ if and only if $x$ is the image of some $b \in B$
under the algebra map $B \to L$. -/
theorem mem_imageOfB {x : L} :
    x ∈ imageOfB A L B ↔ ∃ b : B, algebraMap B L b = x := by
  simp only [imageOfB, Subalgebra.mem_toSubmodule, AlgHom.mem_range,
    IsScalarTower.coe_toAlgHom']

/-- **Elements of $B$ lie in the image of $B$.** Let $A$ and $B$ be commutative rings and $L$ a
field, with algebra maps $A \to B$, $B \to L$ and $A \to L$ forming a scalar tower. For every
$b \in B$, the image of $b$ under the algebra map $B \to L$ lies in the image of $B$ in $L$,
regarded as an $A$-submodule of $L$. -/
theorem algebraMap_mem_imageOfB (b : B) :
    algebraMap B L b ∈ imageOfB A L B :=
  (mem_imageOfB A L B).mpr ⟨b, rfl⟩

/-- The image of a finite A-module B is finite as an A-module. -/
instance imageOfB_finite [Module.Finite A B] :
    Module.Finite A ↥(imageOfB A L B) := by
  have heq : imageOfB A L B =
      (IsScalarTower.toAlgHom A B L).toLinearMap.range := by
    ext x
    constructor
    · intro hx
      rw [mem_imageOfB A L B] at hx
      rcases hx with ⟨b, rfl⟩
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact (mem_imageOfB A L B).mpr ⟨b, rfl⟩
  rw [heq]
  exact Module.Finite.range (IsScalarTower.toAlgHom A B L).toLinearMap

end ImageOfB

section ExtensionDiscriminant

variable (A K : Type*) (L : Type u) (B : Type*)
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L] [FiniteDimensional K L]

/--
**Extension discriminant.** Let $A$ and $B$ be commutative rings and $K$ and $L$ fields with $L$
finite-dimensional over $K$, with algebra maps forming scalar towers $A \to K \to L$ and
$A \to B \to L$, and let $n = [L : K]$. The extension discriminant is the $A$-submodule of $K$
spanned by the discriminants $\operatorname{disc}_{L/K}(b_1, \dots, b_n)$ of all $n$-tuples of
elements of $L$ lying in the image of $B$ in $L$.

At this level of generality it is only an $A$-submodule of $K$, not an ideal of $A$.
-/
def extensionDiscriminant : Submodule A K :=
  latticeDiscriminant A K (imageOfB A L B)

/-- **The extension discriminant is a lattice discriminant.** Let $A$ and $B$ be commutative
rings and $K$ and $L$ fields with $L$ finite-dimensional over $K$, with algebra maps forming
scalar towers $A \to K \to L$ and $A \to B \to L$. The extension discriminant of the tower
equals the lattice discriminant over $A$ and $K$ of the image of $B$ in $L$, regarded as an
$A$-submodule of $L$. -/
theorem extensionDiscriminant_eq :
    extensionDiscriminant A K L B =
      latticeDiscriminant A K (imageOfB A L B) :=
  rfl

/-- **Discriminants of tuples from $B$ lie in the extension discriminant.** Let $A$ and $B$ be
commutative rings and $K$ and $L$ fields with $L$ finite-dimensional over $K$, with algebra maps
forming scalar towers $A \to K \to L$ and $A \to B \to L$, and let $n = [L : K]$. If
$b_1, \dots, b_n \in L$ all lie in the image of $B$ in $L$, then their discriminant
$\operatorname{disc}_{L/K}(b_1, \dots, b_n)$ lies in the extension discriminant of the tower,
an $A$-submodule of $K$. -/
theorem discr_mem_extensionDiscriminant
    {b : Fin (Module.finrank K L) → L} (hb : ∀ i, b i ∈ imageOfB A L B) :
    Algebra.discr K b ∈ extensionDiscriminant A K L B :=
  discr_mem_latticeDiscriminant A K hb

end ExtensionDiscriminant
