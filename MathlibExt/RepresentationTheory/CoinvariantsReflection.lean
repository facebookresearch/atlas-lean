/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Algebra.Exact.Basic

/-!
# Coinvariants detect a representation with invariant augmentation kernel

In an exact equivariant sequence with trivial outer actions, every
augmentation difference in the middle representation is invariant. If its
coinvariants are zero, the middle module is zero. This uses the existing
coinvariants quotient and invariant submodule, for an arbitrary group.

This is the algebraic reflection step for the relative regular-cover
comparison of H-spaces. It does not supply a cover homology, spectral edge
or homotopy-equivalence witness.
-/

open CategoryTheory

universe uK uG uU uV uW

public section

namespace Representation.Coinvariants

variable {k : Type uK} [CommRing k] {G : Type uG} [Group G]
  {U : Type uU} [AddCommGroup U] [Module k U]
  {V : Type uV} [AddCommGroup V] [Module k V]
  {W : Type uW} [AddCommGroup W] [Module k W]

/-- Exact equivariance and trivial outer actions force the original
augmentation kernel of the middle representation to consist of invariants. -/
theorem ker_le_invariants_of_exact
    (sigma : Representation k G U) (rho : Representation k G V)
    (tau : Representation k G W) [sigma.IsTrivial] [tau.IsTrivial]
    (i : IntertwiningMap sigma rho) (q : IntertwiningMap rho tau)
    (hExact : Function.Exact i q) : ker rho ≤ rho.invariants := by
  apply Submodule.span_le.mpr
  intro z hz
  rcases hz with ⟨⟨h, x⟩, rfl⟩
  apply (Representation.mem_invariants rho (rho h x - x)).mpr
  intro g
  have hKernel : q (rho h x - x) = 0 := by
    rw [map_sub,
        Representation.IntertwiningMap.isIntertwining rho tau q h x, tau.isTrivial_apply, sub_self]
  obtain ⟨a, ha⟩ := (hExact (rho h x - x)).mp hKernel
  calc
    rho g (rho h x - x) = rho g (i a) := congrArg (rho g) ha.symm
    _ = i (sigma g a) := (Representation.IntertwiningMap.isIntertwining sigma rho i g a).symm
    _ = i a := congrArg i (sigma.isTrivial_apply g a)
    _ = rho h x - x := ha

/-- The existing coinvariants quotient reflects zero when its augmentation
kernel consists of invariants. No finiteness, flatness or group commutativity is needed. -/
theorem subsingleton_of_ker_le_invariants
    (rho : Representation k G V) (hKernel : ker rho ≤ rho.invariants)
    [Subsingleton (Coinvariants rho)] : Subsingleton V := by
  have hMem (x : V) : x ∈ ker rho :=
    (mk_eq_zero rho).mp (Subsingleton.elim (mk rho x) 0)
  have hFixed (g : G) (x : V) : rho g x = x :=
    (Representation.mem_invariants rho x).mp (hKernel (hMem x)) g
  have hZero : ker rho ≤ (⊥ : Submodule k V) := by
    apply Submodule.span_le.mpr
    intro z hz
    rcases hz with ⟨⟨g, x⟩, rfl⟩
    change rho g x - x ∈ (⊥ : Submodule k V)
    have hDifference : rho g x - x = (0 : V) :=
      (congrArg (fun y : V => y - x) (hFixed g x)).trans (sub_self x)
    exact (Submodule.mem_bot k).mpr hDifference
  have hAllZero (x : V) : x = 0 := (Submodule.mem_bot k).mp (hZero (hMem x))
  exact ⟨fun x y => (hAllZero x).trans (hAllZero y).symm⟩

/-- The middle group of an actual exact equivariant sequence with trivial
ends is zero as soon as its actual coinvariants quotient is zero. -/
theorem subsingleton_of_exact_of_trivial_ends
    (sigma : Representation k G U) (rho : Representation k G V)
    (tau : Representation k G W) [sigma.IsTrivial] [tau.IsTrivial]
    (i : IntertwiningMap sigma rho) (q : IntertwiningMap rho tau)
    (hExact : Function.Exact i q) [Subsingleton (Coinvariants rho)] : Subsingleton V :=
  subsingleton_of_ker_le_invariants rho
    (ker_le_invariants_of_exact sigma rho tau i q hExact)

end Representation.Coinvariants
