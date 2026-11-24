/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.RepresentationTheory.CoinvariantsReflection

open Representation

universe uK uG uU uV uW

#check Representation.Coinvariants.ker_le_invariants_of_exact
#print axioms Representation.Coinvariants.ker_le_invariants_of_exact
#check Representation.Coinvariants.subsingleton_of_ker_le_invariants
#print axioms Representation.Coinvariants.subsingleton_of_ker_le_invariants
#check Representation.Coinvariants.subsingleton_of_exact_of_trivial_ends
#print axioms Representation.Coinvariants.subsingleton_of_exact_of_trivial_ends

namespace CoinvariantsReflectionTests

example {k : Type uK} [CommRing k] {G : Type uG} [Group G]
    {U : Type uU} [AddCommGroup U] [Module k U]
    {V : Type uV} [AddCommGroup V] [Module k V]
    {W : Type uW} [AddCommGroup W] [Module k W]
    (sigma : Representation k G U) (rho : Representation k G V)
    (tau : Representation k G W) [sigma.IsTrivial] [tau.IsTrivial]
    (i : IntertwiningMap sigma rho) (q : IntertwiningMap rho tau)
    (h : Function.Exact i q) [Subsingleton (Coinvariants rho)] (v : V) : v = 0 := by
  let : Subsingleton V := Coinvariants.subsingleton_of_exact_of_trivial_ends sigma rho tau i q h
  exact Subsingleton.elim v 0

/-- The actual coordinate inclusion and projection give the exact sequence;
the action on the middle module is allowed to be nontrivial. -/
example {G : Type uG} [Group G] (rho : Representation ℤ G (ℤ × ℤ))
    (i : IntertwiningMap (Representation.trivial ℤ G ℤ) rho)
    (q : IntertwiningMap rho (Representation.trivial ℤ G ℤ))
    (hi : i.toLinearMap = LinearMap.inl ℤ ℤ ℤ)
    (hq : q.toLinearMap = LinearMap.snd ℤ ℤ ℤ) :
    Coinvariants.ker rho ≤ rho.invariants := by
  have hExact : Function.Exact i q := by
    change Function.Exact i.toLinearMap q.toLinearMap
    rw [hi, hq]
    exact Function.Exact.inl_snd
  exact Coinvariants.ker_le_invariants_of_exact
    (Representation.trivial ℤ G ℤ) rho (Representation.trivial ℤ G ℤ) i q hExact

end CoinvariantsReflectionTests
