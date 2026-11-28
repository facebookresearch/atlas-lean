/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Quandle
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Data.Nat.Totient
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import MathlibExt.Algebra.CyclicHolomorph
public import MathlibExt.Algebra.Quandle
public import MathlibExt.Algebra.VirtualQuandle
public import MathlibExt.Algebra.VirtualRackConjugacy

namespace MetaMathlibExt

@[expose] public section

open Equiv Quandles

/-- **Number of isomorphism classes of virtual racks on a rack.** For a rack $R$, let
$\operatorname{Aut} R$ be its group of rack automorphisms; a virtual structure on $R$ is an
element $f \in \operatorname{Aut} R$, and $(R, f)$ is the corresponding virtual rack. The number
$v(R)$ is the number of classes of virtual structures on $R$, where $f, g \in \operatorname{Aut} R$
are identified when the virtual racks $(R, f)$ and $(R, g)$ are isomorphic; that is, the number
of isomorphism classes of virtual racks with underlying rack $R$. It is $0$ when there are
infinitely many classes.

Every virtual rack whose underlying rack is isomorphic to $R$ is isomorphic to one of the form
$(R, f)$.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Section 3.2.2 (the invariant `v(R)`). -/
noncomputable def virtualRackClassCount (R : Type*) [Rack R] : ℕ :=
  Nat.card (Quot fun f g : rackAut R => VirtualRackIso (f : Perm R) (g : Perm R))

/-- **Reflexivity of virtual rack isomorphism.** For every rack $R$ and every permutation $f$ of
$R$, the pair $(R, f)$ is isomorphic to itself in the sense of virtual rack isomorphism. The
permutation $f$ need not be a rack automorphism.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Section 2.2 (virtual rack isomorphisms). -/
theorem virtualRackIso_refl {R : Type*} [Rack R] (f : Perm R) : VirtualRackIso f f :=
  ⟨Equiv.refl R, fun _ _ => rfl, fun _ => rfl⟩

/-- **Affine maps are automorphisms of the dihedral quandle.** For every natural number $n$,
every $a \in \mathbb{Z}/n\mathbb{Z}$ and every unit $u \in (\mathbb{Z}/n\mathbb{Z})^\times$, the
affine map $T_{a,u} \colon x \mapsto a + u x$ is a rack automorphism of the dihedral quandle
$R_n$, the set $\mathbb{Z}/n\mathbb{Z}$ with $x \triangleleft y = 2x - y$.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Section 2.2 (virtual structures on the dihedral quandle). -/
theorem dihedralAffinePerm_mem_rackAut (n : ℕ) (a : ZMod n) (u : (ZMod n)ˣ) :
    dihedralAffinePerm n a u ∈ rackAut (Quandle.Dihedral n) := by
  change ∀ x y : ZMod n, _ = _
  intro x y
  change a + (u : ZMod n) * (2 * x - y) = 2 * (a + (u : ZMod n) * x) - (a + (u : ZMod n) * y)
  ring

/-- **Virtual quandle structures on the dihedral quandle.** For every $n > 0$, the number
$v(R_n)$ of isomorphism classes of virtual racks whose underlying rack is the dihedral quandle
$R_n$ (the set $\mathbb{Z}/n\mathbb{Z}$ with $x \triangleleft y = 2x - y$) equals
$\varphi(n) \sum_{d \mid n} 1/\varphi(d)$, where $\varphi$ is Euler's totient function.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Theorem 1 (`jis-2025-25.8.4-thm-1`). -/
public theorem_wanted virtualRackClassCount_dihedral (n : ℕ) (hn : 0 < n) :
    (virtualRackClassCount (Quandle.Dihedral n) : ℚ) =
      n.totient * ∑ d ∈ n.divisors, (1 : ℚ) / d.totient

end

end MetaMathlibExt
