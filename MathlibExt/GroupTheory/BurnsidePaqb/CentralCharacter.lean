/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import MathlibExt.GroupTheory.BurnsidePaqb.ClassSum

/-!
Central-character stage of the complete Burnside proof.

Authors: Muse Spark 1.3
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is mechanically ported from the audited source `extracted/Burnside/CentralChar.lean`.
-/

namespace BurnsidePaqb

@[expose] public section

variable {G : Type*} [Group G] [Fintype G]

omit [Fintype G] in
/-- **Schur's lemma for central elements of the group algebra.** Let $\rho$ be an irreducible
representation of a group $G$ on a finite-dimensional complex vector space $V$, extended linearly
to the group algebra $\mathbb{C}[G]$. If $z \in \mathbb{C}[G]$ commutes with every element of
$\mathbb{C}[G]$, then $z$ acts on $V$ as a scalar: there is $c \in \mathbb{C}$ with
$\rho(z) v = c\, v$ for all $v \in V$. -/
theorem exists_scalar_of_central {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    [Representation.IsIrreducible ρ]
    (z : MonoidAlgebra ℂ G) (hz : ∀ w, w * z = z * w) :
    ∃ c : ℂ, ∀ v : V, ρ.asAlgebraHom z v = c • v := by
  classical
  let L : Module.End (MonoidAlgebra ℂ G) ρ.asModule :=
    { toFun := fun v => z • v
      map_add' := fun x y => smul_add z x y
      map_smul' := fun r x => by
        change z • (r • x) = r • (z • x)
        rw [← smul_assoc, ← smul_assoc]
        change (z * r) • x = (r * z) • x
        rw [(hz r).symm] }
  obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed ℂ).2 L
  refine ⟨c, fun v => ?_⟩
  have h1 : (algebraMap ℂ (Module.End (MonoidAlgebra ℂ G) ρ.asModule) c)
      (ρ.asModuleEquiv.symm v) = L (ρ.asModuleEquiv.symm v) := by rw [hc]
  have h2 : ∀ x : ρ.asModule,
      (algebraMap ℂ (Module.End (MonoidAlgebra ℂ G) ρ.asModule) c) x = c • x := by
    intro x
    simp [Algebra.algebraMap_eq_smul_one]
  have hL : ∀ x : ρ.asModule, L x = z • x := fun x => rfl
  rw [h2, hL] at h1
  have h4 : ρ.asModuleEquiv (c • ρ.asModuleEquiv.symm v) =
      ρ.asModuleEquiv (z • ρ.asModuleEquiv.symm v) := congrArg _ h1
  rw [map_smul, LinearEquiv.apply_symm_apply, ρ.asModuleEquiv_map_smul,
    LinearEquiv.apply_symm_apply] at h4
  exact h4.symm

section CentralScalar

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]

open Classical in
/-- **Central scalar of a conjugacy class.** Let $\rho$ be an irreducible representation of a
finite group $G$ on a finite-dimensional complex vector space $V$. For a conjugacy class $C$ of
$G$, the class sum $\sum_{x \in C} x$ is central in the group algebra $\mathbb{C}[G]$, so it acts
on $V$ as multiplication by a complex number. The central scalar $\omega_\rho(C)$ is that number:
$\rho\bigl(\sum_{x \in C} x\bigr) v = \omega_\rho(C)\, v$ for all $v \in V$. -/
noncomputable def centralScalar (l : ConjClasses G) : ℂ :=
  Classical.choose
    (exists_scalar_of_central ρ (classSum (ConjClasses.carrier l).toFinset)
      (classSum_carrier_central l))

open Classical in
theorem centralScalar_spec (l : ConjClasses G) (v : V) :
    ρ.asAlgebraHom (classSum (ConjClasses.carrier l).toFinset) v
      = centralScalar ρ l • v :=
  Classical.choose_spec
    (exists_scalar_of_central ρ (classSum (ConjClasses.carrier l).toFinset)
      (classSum_carrier_central l)) v

open Classical in
/-- **Central scalars multiply via the class structure constants.** Let $\rho$ be an irreducible
representation of a finite group $G$ on a finite-dimensional complex vector space $V$, and let
$\omega_\rho(C)$ be the scalar by which the class sum of a conjugacy class $C$ acts on $V$. Fix
a representative $g_C$ of each conjugacy class $C$. For conjugacy classes $C_1$ and $C_2$,

$$\omega_\rho(C_1)\,\omega_\rho(C_2) = \sum_{C} a_{C_1 C_2}^{C}\, \omega_\rho(C),$$

where $C$ runs over all conjugacy classes of $G$ and $a_{C_1 C_2}^{C}$ is the number of pairs
$(x, y) \in C_1 \times C_2$ with $x y = g_C$. -/
theorem centralScalar_mul (l1 l2 : ConjClasses G) :
    centralScalar ρ l1 * centralScalar ρ l2
      = ∑ l, (structConst (conjClass (classRep l1)) (conjClass (classRep l2))
          (classRep l) : ℂ) * centralScalar ρ l := by
  classical
  have hend : ρ.asAlgebraHom (classSum (ConjClasses.carrier l1).toFinset)
        * ρ.asAlgebraHom (classSum (ConjClasses.carrier l2).toFinset)
      = ∑ l, (structConst (conjClass (classRep l1)) (conjClass (classRep l2))
          (classRep l) : ℂ)
          • ρ.asAlgebraHom (classSum (ConjClasses.carrier l).toFinset) := by
    rw [carrier_toFinset, carrier_toFinset, ← map_mul, classSum_mul, map_sum]
    simp only [map_smul]
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hpoint : (ρ.asAlgebraHom (classSum (ConjClasses.carrier l1).toFinset)
        * ρ.asAlgebraHom (classSum (ConjClasses.carrier l2).toFinset)) v
      = (∑ l, (structConst (conjClass (classRep l1)) (conjClass (classRep l2))
          (classRep l) : ℂ)
          • ρ.asAlgebraHom (classSum (ConjClasses.carrier l).toFinset)) v :=
    congrArg (fun F : Module.End ℂ V => F v) hend
  rw [Module.End.mul_apply, LinearMap.sum_apply] at hpoint
  simp only [LinearMap.smul_apply, centralScalar_spec, smul_smul] at hpoint
  rw [← Finset.sum_smul] at hpoint
  have hsub : (centralScalar ρ l1 * centralScalar ρ l2
      - ∑ l, (structConst (conjClass (classRep l1)) (conjClass (classRep l2))
          (classRep l) : ℂ) * centralScalar ρ l) • v = 0 := by
    rw [sub_smul, hpoint, sub_self]
  rcases smul_eq_zero.mp hsub with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hv

open Classical in
/-- **Trace formula for central scalars.** Let $\rho$ be an irreducible representation of a
finite group $G$ on a finite-dimensional complex vector space $V$ with character $\chi$, and let
$\omega_\rho(C)$ be the scalar by which the class sum of a conjugacy class $C$ acts on $V$. Then
$\omega_\rho(C) \cdot \dim V = \sum_{x \in C} \chi(x)$. -/
theorem centralScalar_trace (l : ConjClasses G) :
    centralScalar ρ l * Module.finrank ℂ V
      = ∑ x ∈ (ConjClasses.carrier l).toFinset, ρ.character x := by
  classical
  have hT : ρ.asAlgebraHom (classSum (ConjClasses.carrier l).toFinset)
      = centralScalar ρ l • 1 := by
    ext v
    simp [centralScalar_spec]
  have htrace : LinearMap.trace ℂ V
        (ρ.asAlgebraHom (classSum (ConjClasses.carrier l).toFinset))
      = centralScalar ρ l * Module.finrank ℂ V := by
    have hid : (1 : Module.End ℂ V) = LinearMap.id := rfl
    rw [hT, map_smul, hid, LinearMap.trace_id, smul_eq_mul]
  have hexpand : ρ.asAlgebraHom (classSum (ConjClasses.carrier l).toFinset)
      = ∑ x ∈ (ConjClasses.carrier l).toFinset, ρ x := by
    change ρ.asAlgebraHom (∑ x ∈ (ConjClasses.carrier l).toFinset,
        MonoidAlgebra.of ℂ G x) = _
    rw [map_sum]
    simp only [Representation.asAlgebraHom_of]
  have hsum : LinearMap.trace ℂ V
        (ρ.asAlgebraHom (classSum (ConjClasses.carrier l).toFinset))
      = ∑ x ∈ (ConjClasses.carrier l).toFinset, ρ.character x := by
    rw [hexpand, map_sum]
    rfl
  rw [← htrace, hsum]

open Classical in
/-- **Generators of the central-scalar ring.** Let $\rho$ be an irreducible representation of a
finite group $G$ on a finite-dimensional complex vector space $V$, and let $\omega_\rho(C)$ be
the scalar by which the class sum of a conjugacy class $C$ acts on $V$. The set $S_\rho$ is the
finite set of complex numbers consisting of $1$ and the values $\omega_\rho(C)$ for all
conjugacy classes $C$ of $G$. -/
noncomputable def scalarGens : Finset ℂ :=
  insert 1 (Finset.univ.image (centralScalar ρ))

open Classical in
theorem one_mem_scalarSpan : (1 : ℂ) ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) :=
  Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_insert_self 1 _))

open Classical in
theorem scalar_mem_scalarSpan (l : ConjClasses G) :
    centralScalar ρ l ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) :=
  Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem _ (Finset.mem_univ l))))

open Classical in
/-- **Products of central-scalar generators stay in their span.** Let $\rho$ be an irreducible
representation of a finite group $G$ on a finite-dimensional complex vector space $V$, and let
$S_\rho$ be the finite set of complex numbers consisting of $1$ and the scalars by which the
class sums of the conjugacy classes of $G$ act on $V$. If $a, b \in S_\rho$, then $ab$ lies in
the $\mathbb{Z}$-linear span of $S_\rho$. -/
theorem scalarGens_mul (a b : ℂ) (ha : a ∈ scalarGens ρ) (hb : b ∈ scalarGens ρ) :
    a * b ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) := by
  classical
  rw [scalarGens, Finset.mem_insert, Finset.mem_image] at ha hb
  rcases ha with rfl | ⟨l1, _, rfl⟩ <;> rcases hb with rfl | ⟨l2, _, rfl⟩
  · simpa using one_mem_scalarSpan ρ
  · simp only [one_mul]
    exact scalar_mem_scalarSpan ρ l2
  · simp only [mul_one]
    exact scalar_mem_scalarSpan ρ l1
  · rw [centralScalar_mul]
    apply sum_mem
    intro l _
    have hsmul : ∀ (n : ℕ) (x : ℂ), (n : ℂ) * x = (n : ℤ) • x := by
      intro n x
      exact (zsmul_eq_mul x n).symm
    rw [hsmul]
    exact Submodule.smul_mem _ _ (scalar_mem_scalarSpan ρ l)

open Classical in
/-- **Ring generated by the central scalars.** Let $\rho$ be an irreducible representation of a
finite group $G$ on a finite-dimensional complex vector space $V$, and let $S_\rho$ be the finite
set of complex numbers consisting of $1$ and the scalars by which the class sums of the
conjugacy classes of $G$ act on $V$. The $\mathbb{Z}$-linear span of $S_\rho$ is closed under
multiplication, and this is that span as a $\mathbb{Z}$-subalgebra of $\mathbb{C}$. -/
noncomputable def scalarSubalg : Subalgebra ℤ ℂ where
  carrier := ↑(Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ))
  mul_mem' := by
    intro x y hx hy
    have hx' : x ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) := hx
    have hy' : y ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) := hy
    suffices h : x * y ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) from h
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx'
    · intro z hz
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy'
      · intro w hw
        exact scalarGens_mul ρ z w (Finset.mem_coe.mp hz) (Finset.mem_coe.mp hw)
      · rw [mul_zero]
        exact Submodule.zero_mem _
      · intro a b ha hb iha ihb
        rw [mul_add]
        exact add_mem iha ihb
      · intro c b hb ih
        rw [mul_smul_comm]
        exact Submodule.smul_mem _ _ ih
    · rw [zero_mul]
      exact Submodule.zero_mem _
    · intro a b ha hb iha ihb
      rw [add_mul]
      exact add_mem iha ihb
    · intro c a ha ih
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ _ ih
  one_mem' := one_mem_scalarSpan ρ
  add_mem' := by
    intro x y hx hy
    have hx' : x ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) := hx
    have hy' : y ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) := hy
    have h : x + y ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) :=
      Submodule.add_mem _ hx' hy'
    exact h
  zero_mem' := Submodule.zero_mem _
  algebraMap_mem' := by
    intro n
    have h1 : algebraMap ℤ ℂ n = n • (1 : ℂ) := by
      rw [Algebra.smul_def, mul_one]
    rw [h1]
    exact Submodule.smul_mem _ _ (one_mem_scalarSpan ρ)

open Classical in
theorem scalarSubalg_fg : (scalarSubalg ρ).toSubmodule.FG := by
  classical
  have : (scalarSubalg ρ).toSubmodule
      = Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) := rfl
  rw [this]
  exact ⟨scalarGens ρ, rfl⟩

open Classical in
/-- **Central scalars are algebraic integers.** Let $\rho$ be an irreducible representation of a
finite group $G$ on a finite-dimensional complex vector space $V$. For every conjugacy class $C$
of $G$, the complex number $\omega_\rho(C)$ by which the class sum $\sum_{x \in C} x$ acts on $V$
is an algebraic integer, that is, integral over $\mathbb{Z}$. -/
theorem centralScalar_isIntegral (l : ConjClasses G) :
    IsIntegral ℤ (centralScalar ρ l) :=
  IsIntegral.of_mem_of_fg (scalarSubalg ρ) (scalarSubalg_fg ρ) _
    (scalar_mem_scalarSpan ρ l)

open Classical in
/-- **Class size times character ratio is an algebraic integer.** Let $\rho$ be an irreducible
representation of a finite group $G$ on a finite-dimensional complex vector space $V$, with
character $\chi$. For every $g \in G$, if $C$ is the conjugacy class of $g$, then
$|C|\,\chi(g)/\chi(1)$ is an algebraic integer.

Source: Bielefeld Prop 1. -/
theorem classSum_centralScalar_isIntegral (g : G) :
    IsIntegral ℤ ((conjClass g).card * ρ.character g / ρ.character 1) := by
  classical
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  have hpos : 0 < Module.finrank ℂ V := Module.finrank_pos
  have hχ1ne : ρ.character 1 ≠ 0 := by
    rw [Representation.char_one]
    exact_mod_cast ne_of_gt hpos
  have hdiv : centralScalar ρ (ConjClasses.mk g)
      = (conjClass g).card * ρ.character g / ρ.character 1 := by
    rw [eq_div_iff hχ1ne]
    have hcarry : (ConjClasses.carrier (ConjClasses.mk g)).toFinset
        = conjClass g := by
      rw [carrier_toFinset]
      apply conjClass_eq_of_isConj
      rw [← ConjClasses.mk_eq_mk_iff_isConj]
      exact classRep_spec _
    have hchar : ∀ x ∈ conjClass g, ρ.character x = ρ.character g := by
      intro x hx
      rw [mem_conjClass_iff] at hx
      obtain ⟨c, hc⟩ := isConj_iff.mp hx
      have hcc := Representation.char_conj ρ x c
      rw [hc] at hcc
      exact hcc.symm
    have hsum : ∑ x ∈ conjClass g, ρ.character x
        = (conjClass g).card * ρ.character g := by
      calc ∑ x ∈ conjClass g, ρ.character x
            = ∑ x ∈ conjClass g, ρ.character g :=
              Finset.sum_congr rfl (fun x hx => hchar x hx)
        _ = (conjClass g).card * ρ.character g := by
              rw [Finset.sum_const, nsmul_eq_mul]
    have htrace := centralScalar_trace ρ (ConjClasses.mk g)
    rw [hcarry, hsum] at htrace
    rw [Representation.char_one]
    exact htrace
  rw [← hdiv]
  exact centralScalar_isIntegral ρ _

end CentralScalar

end

end BurnsidePaqb
