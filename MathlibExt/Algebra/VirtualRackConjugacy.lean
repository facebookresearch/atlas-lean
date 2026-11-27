/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Conj
public import MathlibExt.Algebra.Quandle

/-!
# Conjugacy of virtual rack structures

For a fixed rack, virtual structures are isomorphic precisely when they are conjugate in its
rack automorphism group.

## References

* Lực Ta, *Enumeration of Virtual Quandles up to Isomorphism*, Journal of Integer Sequences 28
  (2025), Article 25.8.4, pp. 1–11, Definition 13 (§2.2) and Proposition 14 (§3.1).
* V. O. Manturov, *On Invariants of Virtual Links*, Acta Applicandae Mathematica 72 (2002),
  no. 3, pp. 295–309, for the original notion of virtual racks, as credited in Ta, §1.1.
* Roger Fenn and Colin Rourke, *Racks and Links in Codimension Two*, Journal of Knot Theory and
  Its Ramifications 1 (1992), no. 4, pp. 343–406, for the underlying rack structure, as credited
  in Ta, §1.1.
-/

namespace MetaMathlibExt

@[expose] public section

open Equiv Quandles

/-- **Isomorphism of virtual racks.** Write $x \triangleleft y$ for the operation of a rack. A
virtual rack $(R, f)$ is a rack $R$ together with a rack automorphism $f$ of $R$, its virtual
structure. Let $R_1$ and $R_2$ be racks and let $f_1$ and $f_2$ be permutations of $R_1$ and
$R_2$. Then $(R_1, f_1)$ and $(R_2, f_2)$ are isomorphic when there is a bijection
$\psi \colon R_1 \to R_2$ such that $\psi(x \triangleleft y) = \psi(x) \triangleleft \psi(y)$
for all $x, y \in R_1$ and $\psi(f_1(x)) = f_2(\psi(x))$ for all $x \in R_1$.

The definition does not require $f_1$ and $f_2$ to be rack automorphisms; for virtual racks it
is the usual notion of isomorphism.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Section 2.2 (virtual rack isomorphisms). -/
def VirtualRackIso {R₁ R₂ : Type*} [Rack R₁] [Rack R₂] (f₁ : Perm R₁) (f₂ : Perm R₂) : Prop :=
  ∃ ψ : R₁ ≃ R₂, (∀ x y, ψ (x ◃ y) = ψ x ◃ ψ y) ∧ ∀ x, ψ (f₁ x) = f₂ (ψ x)

/-- **Isomorphism of virtual structures is conjugacy.** Let $R$ be a rack and let $f_1$ and $f_2$
be elements of its automorphism group $\operatorname{Aut} R$. Then the virtual racks $(R, f_1)$
and $(R, f_2)$ are isomorphic if and only if $f_1$ and $f_2$ are conjugate in
$\operatorname{Aut} R$.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Proposition 14 (`jis-2025-25.8.4-prop-14`). -/
public theorem virtualRackIso_iff_isConj {R : Type*} [Rack R] (f₁ f₂ : rackAut R) :
    VirtualRackIso (f₁ : Perm R) (f₂ : Perm R) ↔ IsConj f₁ f₂ := by
  simp only [isConj_iff, mul_inv_eq_iff_eq_mul]
  constructor
  · rintro ⟨ψ, hψ, hcomm⟩
    refine ⟨⟨ψ, hψ⟩, ?_⟩
    apply Subtype.ext
    exact Equiv.ext hcomm
  · rintro ⟨ψ, hcomm⟩
    refine ⟨ψ.val, ψ.property, fun x => ?_⟩
    exact Equiv.congr_fun (congrArg (fun g : rackAut R => (g : Perm R)) hcomm) x

end

end MetaMathlibExt
