/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Dehn invariant

The **Dehn invariant** of a polyhedron is the sum, over its edges, of
`length ⊗ₜ dihedral angle` in the **Dehn group** `ℝ ⊗[ℤ] (ℝ / 2πℤ)`.
By the Dehn–Sydler theorem, two polyhedra of equal volume are scissors-congruent
if and only if they have the same Dehn invariant.

This file defines the Dehn invariant for a list of edges and proves its
two classical values:

* `dehnInvariant_cubeEdges`: the cube has Dehn invariant `0`, since each
  of its 12 dihedral angles is `π / 2` and `12 • (π / 2) = 3 • (2π)` vanishes
  in `ℝ / 2πℤ`.
* `dehnInvariant_tetrahedronEdges_ne_zero`: the regular tetrahedron has
  nonzero Dehn invariant, conditional on the irrationality of
  `arccos (1 / 3) / π` (taken as a hypothesis: it follows from a short
  algebraic-integer argument, not carried out here).

Hence, under that irrationality hypothesis, the cube and the regular tetrahedron
have different Dehn invariants, so they are not scissors-congruent.

Source: `v1/Atlas/AlgebraNotes/code/DehnInvariant.lean` (targets
`DehnInvariant.dehnInvariant`, `DehnInvariant.dehn_cube`,
`DehnInvariant.dehn_tetrahedron_ne_zero`,
`DehnInvariant.dehn_cube_ne_dehn_tetrahedron` in
`v1/Atlas/AlgebraNotes/targets.yaml` / `report.json`). The v1 file proved the
tetrahedron claims from an unproved irrationality lemma; here irrationality is
an explicit hypothesis, so every proof is complete. The v1 `tensorProduct` /
`tmul` wrappers around `TensorProduct` are dropped in favour of Mathlib's API.
-/

@[expose] public section

namespace DehnInvariant

open Real
open scoped TensorProduct

/-- **Dehn group.** The Dehn group is the tensor product
$\mathbb{R} \otimes_{\mathbb{Z}} (\mathbb{R} / 2\pi\mathbb{Z})$ of abelian groups; it is the target
of the Dehn invariant. -/
abbrev DehnGroup : Type := ℝ ⊗[ℤ] AddCircle (2 * π)

/-- **Edge of a polyhedron.** An edge, as recorded for the Dehn invariant, is a pair of real
numbers: its length and its dihedral angle in radians. No positivity or range condition is
imposed on either. -/
structure Edge where
  /-- The length of the edge. -/
  length : ℝ
  /-- The dihedral angle at the edge, in radians. -/
  angle : ℝ

/-- **Dehn invariant.** The Dehn invariant of a list of edges is the sum, over the edges, of
$\ell \otimes \theta$ in the Dehn group, where $\ell$ is the length of the edge and $\theta$ its
dihedral angle taken modulo $2\pi$. -/
noncomputable def dehnInvariant (edges : List Edge) : DehnGroup :=
  (edges.map (fun e => e.length ⊗ₜ[ℤ] (↑e.angle : AddCircle (2 * π)))).sum

/-- **Dihedral angle of the regular tetrahedron.** The real number $\arccos(1/3)$, the dihedral
angle of a regular tetrahedron in radians. -/
noncomputable def tetrahedralAngle : ℝ := arccos (1 / 3)

/-- **Edge list of a cube.** For a real number $\ell$, the edge list of a cube of side $\ell$
consists of $12$ edges, each of length $\ell$ with dihedral angle $\pi / 2$. -/
noncomputable def cubeEdges (ℓ : ℝ) : List Edge := List.replicate 12 ⟨ℓ, π / 2⟩

/-- **Edge list of the regular tetrahedron.** For a real number $\ell$, the edge list of a
regular tetrahedron with edge length $\ell$ is the list of $6$ edges, each of length $\ell$ and
dihedral angle $\arccos(1/3)$. -/
noncomputable def tetrahedronEdges (ℓ : ℝ) : List Edge :=
  List.replicate 6 ⟨ℓ, tetrahedralAngle⟩

/-- **Dehn invariant of the empty edge list.** The empty list of edges has Dehn invariant $0$. -/
@[simp]
theorem dehnInvariant_nil : dehnInvariant [] = 0 := rfl

/-- **The Dehn invariant splits off the first edge.** Let $e$ be an edge of length $\ell$ and
dihedral angle $\theta$, and let $L$ be a list of edges. Then the Dehn invariant of the list
obtained by putting $e$ in front of $L$ equals $\ell \otimes \theta$ plus the Dehn invariant of
$L$, where $\theta$ is taken modulo $2\pi$. -/
@[simp]
theorem dehnInvariant_cons (e : Edge) (edges : List Edge) :
    dehnInvariant (e :: edges) =
      e.length ⊗ₜ[ℤ] (↑e.angle : AddCircle (2 * π)) + dehnInvariant edges := rfl

/-- **Additivity of the Dehn invariant under concatenation.** For lists of edges $L_1$ and $L_2$,
the Dehn invariant of the concatenation of $L_1$ and $L_2$ is the sum of the Dehn invariants of
$L_1$ and $L_2$. -/
@[simp]
theorem dehnInvariant_append (edges₁ edges₂ : List Edge) :
    dehnInvariant (edges₁ ++ edges₂) = dehnInvariant edges₁ + dehnInvariant edges₂ := by
  simp [dehnInvariant, List.map_append, List.sum_append]

/-- **Dehn invariant of a repeated edge.** For a natural number $n$ and an edge of length $\ell$
and dihedral angle $\theta$, the Dehn invariant of the list consisting of $n$ copies of that edge
is $n \cdot (\ell \otimes \theta)$ in the Dehn group, where $\theta$ is taken modulo $2\pi$. -/
theorem dehnInvariant_replicate (n : ℕ) (e : Edge) :
    dehnInvariant (List.replicate n e) =
      n • (e.length ⊗ₜ[ℤ] (↑e.angle : AddCircle (2 * π))) := by
  simp [dehnInvariant, List.map_replicate, List.sum_replicate]

/-- The additive homomorphism `AddCircle (2π) →+ ℝ` induced by a `ℚ`-linear map
`f : ℝ →ₗ[ℚ] ℝ` with `f π = 0`. Helper for `tmul_ne_zero_of_irrational`. -/
private noncomputable def fBar (f : ℝ →ₗ[ℚ] ℝ) (hf_pi : f π = 0) :
    AddCircle (2 * π) →+ ℝ :=
  QuotientAddGroup.lift (AddSubgroup.zmultiples (2 * π)) f.toAddMonoidHom (by
    intro x hx
    rw [AddMonoidHom.mem_ker]
    obtain ⟨n, hn⟩ := (AddSubgroup.mem_zmultiples_iff).mp hx
    rw [← hn]; change f (n • (2 * π)) = 0
    have h2pi : f (2 * π) = 0 := by
      have : (2 : ℝ) * π = π + π := by ring
      rw [this, map_add, hf_pi, add_zero]
    rw [map_zsmul, h2pi, smul_zero])

/-- `fBar f hf_pi` acts as `f` on representatives. -/
@[simp]
private lemma fBar_mk (f : ℝ →ₗ[ℚ] ℝ) (hf_pi : f π = 0) (x : ℝ) :
    fBar f hf_pi (↑x : AddCircle (2 * π)) = f x := by
  simp [fBar, QuotientAddGroup.lift_mk]

/-- **A $\mathbb{Q}$-linear functional separating $\alpha$ from $\pi$.** Let $\alpha$ be a real
number such that $\alpha / \pi$ is irrational. Then there is a $\mathbb{Q}$-linear map
$f : \mathbb{R} \to \mathbb{R}$ with $f(\pi) = 0$ and $f(\alpha) \neq 0$.

The idea of the proof: $\alpha$ lies outside the $\mathbb{Q}$-span of $\pi$, and a linear
functional on the quotient separates it. -/
theorem exists_linearMap_of_irrational {α : ℝ} (hirr : Irrational (α / π)) :
    ∃ f : ℝ →ₗ[ℚ] ℝ, f π = 0 ∧ f α ≠ 0 := by
  set S := Submodule.span ℚ ({π} : Set ℝ)
  have hα_not : α ∉ S := by
    rw [Submodule.mem_span_singleton]
    intro ⟨q, hq⟩
    have key : (q : ℝ) * π = α := by
      change q • π = α at hq; rwa [Rat.smul_def] at hq
    have : α / π = (q : ℝ) := by field_simp; linarith
    exact hirr ⟨q, this.symm⟩
  have hα_quot : (Submodule.Quotient.mk (p := S) α) ≠ 0 := by
    rwa [ne_eq, Submodule.Quotient.mk_eq_zero]
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero ℚ hα_quot
  refine ⟨(Algebra.linearMap ℚ ℝ).comp (φ.comp S.mkQ), ?_, ?_⟩
  · simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
    have : (Submodule.Quotient.mk (p := S) π) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span (Set.mem_singleton π)
    simp [this]
  · simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
    intro h
    apply hφ
    have : (φ (Submodule.Quotient.mk α) : ℝ) = 0 := h
    exact_mod_cast this

/-- **Nonvanishing of an edge term in the Dehn group.** Let $\ell$ and $\alpha$ be real numbers
with $\ell \neq 0$ and $\alpha / \pi$ irrational. Then the pure tensor $\ell \otimes [\alpha]$ is
nonzero in the Dehn group $\mathbb{R} \otimes_{\mathbb{Z}} (\mathbb{R} / 2\pi\mathbb{Z})$, where
$[\alpha]$ is the class of $\alpha$ modulo $2\pi$.

The proof applies a $\mathbb{Q}$-linear functional that vanishes at $\pi$ but not at $\alpha$. -/
theorem tmul_ne_zero_of_irrational {α : ℝ} {ℓ : ℝ}
    (hℓ : ℓ ≠ 0) (hirr : Irrational (α / π)) :
    ℓ ⊗ₜ[ℤ] (↑α : AddCircle (2 * π)) ≠ (0 : DehnGroup) := by
  obtain ⟨f, hfπ, hfα⟩ := exists_linearMap_of_irrational hirr
  intro h
  have := congr_arg (TensorProduct.liftAddHom (R := ℤ)
    { toFun := fun x => {
        toFun := fun y => x * (fBar f hfπ y)
        map_zero' := by simp
        map_add' := by intro a b; simp [mul_add] }
      map_zero' := by ext; simp
      map_add' := by intro a b; ext y; simp [add_mul] }
    (by intro n x y; simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        rw [zsmul_eq_mul, map_zsmul, zsmul_eq_mul]; ring)) h
  simp only [TensorProduct.liftAddHom_tmul, map_zero, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    fBar_mk] at this
  exact absurd this (mul_ne_zero hℓ hfα)

/-- The single edge term for a cube edge vanishes after taking 12 copies:
`12 • (π / 2) = 3 • (2π)` is `0` in `ℝ / 2πℤ`. -/
private theorem smul_tmul_pi_div_two_eq_zero (ℓ : ℝ) :
    ((12 : ℤ) • ℓ) ⊗ₜ[ℤ] (↑(π / 2) : AddCircle (2 * π)) = (0 : DehnGroup) := by
  rw [← TensorProduct.smul_tmul', ← TensorProduct.tmul_smul]
  change ℓ ⊗ₜ[ℤ] ((12 : ℤ) • (↑(π / 2) : AddCircle (2 * π))) = 0
  have key : (12 : ℤ) • (↑(π / 2) : AddCircle (2 * π)) = 0 := by
    rw [← AddCircle.coe_zsmul (2 * π)]
    simp only [zsmul_eq_mul, Int.cast_ofNat]
    rw [show (12 : ℝ) * (π / 2) = 3 * (2 * π) from by ring, AddCircle.coe_eq_zero_iff]
    exact ⟨3, by ring⟩
  rw [key, TensorProduct.tmul_zero]

/-- **The Dehn invariant of the cube is zero.** For every real number $\ell$, the edge list of a
cube of side $\ell$ (twelve edges of length $\ell$, each with dihedral angle $\pi / 2$) has Dehn
invariant $0$.

The reason is that $12 \cdot (\pi / 2) = 3 \cdot 2\pi$ vanishes in $\mathbb{R} / 2\pi\mathbb{Z}$. -/
theorem dehnInvariant_cubeEdges (ℓ : ℝ) : dehnInvariant (cubeEdges ℓ) = 0 := by
  show dehnInvariant (List.replicate 12 ⟨ℓ, π / 2⟩) = 0
  rw [dehnInvariant_replicate]
  show (12 : ℕ) • (ℓ ⊗ₜ[ℤ] (↑(π / 2) : AddCircle (2 * π))) = 0
  rw [← Nat.cast_smul_eq_nsmul ℤ, TensorProduct.smul_tmul']
  exact smul_tmul_pi_div_two_eq_zero ℓ

/-- **Nonzero Dehn invariant of the regular tetrahedron, conditional on irrationality.** Suppose
that $\arccos(1/3) / \pi$ is irrational. Then for every nonzero real number $\ell$, the edge list
of a regular tetrahedron of side $\ell$ (six edges of length $\ell$, each with dihedral angle
$\arccos(1/3)$) has nonzero Dehn invariant. -/
theorem dehnInvariant_tetrahedronEdges_ne_zero {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    (hirr : Irrational (tetrahedralAngle / π)) :
    dehnInvariant (tetrahedronEdges ℓ) ≠ 0 := by
  show dehnInvariant (List.replicate 6 ⟨ℓ, tetrahedralAngle⟩) ≠ 0
  rw [dehnInvariant_replicate]
  show (6 : ℕ) • (ℓ ⊗ₜ[ℤ] (↑tetrahedralAngle : AddCircle (2 * π))) ≠ 0
  rw [← Nat.cast_smul_eq_nsmul ℤ, TensorProduct.smul_tmul']
  have h6ℓ : (6 : ℤ) • ℓ ≠ 0 := by simp [hℓ]
  exact tmul_ne_zero_of_irrational h6ℓ hirr

/-- **Conditionally, the cube and the regular tetrahedron have different Dehn invariants.**
Suppose that $\arccos(1/3) / \pi$ is irrational. Then for all real numbers $\ell$ and $\ell'$ with
$\ell' \ne 0$, the edge list of a cube of side $\ell$ and the edge list of a regular tetrahedron
of side $\ell'$ have different Dehn invariants.

Since scissors-congruent polyhedra have equal Dehn invariants, under this hypothesis a cube and a
regular tetrahedron of equal volume are not scissors-congruent. -/
theorem dehnInvariant_cube_ne_dehnInvariant_tetrahedron {ℓ ℓ' : ℝ} (hℓ' : ℓ' ≠ 0)
    (hirr : Irrational (tetrahedralAngle / π)) :
    dehnInvariant (cubeEdges ℓ) ≠ dehnInvariant (tetrahedronEdges ℓ') := by
  intro h
  rw [dehnInvariant_cubeEdges] at h
  exact dehnInvariant_tetrahedronEdges_ne_zero hℓ' hirr h.symm

end DehnInvariant
