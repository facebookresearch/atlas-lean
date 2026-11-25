/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Uniform
public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Normalization
public import MathlibExt.Topology.ContinuousMap.ZeroAtInfty.Postcomp
public import MathlibExt.Topology.ContinuousMap.ZeroAtInfty.Flip

public import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Uniform asymptotic morphisms on functions vanishing at infinity

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let φ be an asymptotic star morphism A→B, a family φ_t:A→B with continuous
time orbits and vanishing additive, complex-scalar, multiplicative and star defects as t→∞.
Assume a↦(t↦φ_t(a)) is continuous from A into C_b(T,B) with its supremum norm; this is
IsUniform φ. For any topological space X, zero normalization φ0_t(a)=φ_t(a)-φ_t(0) acts on
C₀(X,A) by F_t(f)(x)=φ0_t(f(x)). The resulting asymptotic morphism C₀(X,A)→C₀(X,B) is uniform;
its four defects converge in the supremum norm over X.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped ZeroAtInfty BoundedContinuousFunction UniformConvergence

universe uA uB uX

namespace AsymptoticMorphism

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- **Zero normalization preserves uniformity.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let φ be an asymptotic star morphism A→B, a family φ_t:A→B with continuous
time orbits and vanishing additive, complex-scalar, multiplicative and star defects as t→∞.
Assume a↦(t↦φ_t(a)) is continuous from A into C_b(T,B) with its supremum norm; this is
IsUniform φ. The family normalize φ, with values φ_t(a)-φ_t(0), also satisfies IsUniform:
a↦(t↦φ_t(a)-φ_t(0)) is continuous into C_b(T,B).
-/
theorem IsUniform.normalize {φ : AsymptoticMorphism A B} (hφ : IsUniform φ) :
    IsUniform (AsymptoticMorphism.normalize φ) := by
  rcases hφ with ⟨F, hF⟩
  let F' : C(A, AsymptoticTime →ᵇ B) :=
    { toFun := fun a => F a - F 0
      continuous_toFun := (map_continuous F).fun_sub continuous_const }
  refine ⟨F', ?_⟩
  intro t a
  change (F a - F (0 : A)) t = AsymptoticMorphism.normalize φ t a
  rw [BoundedContinuousFunction.sub_apply, hF t a, hF t 0, normalize_apply]

/-- **Continuous bounded-orbit map on C₀ functions.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let φ be an asymptotic star morphism A→B, a family φ_t:A→B with continuous
time orbits and vanishing additive, complex-scalar, multiplicative and star defects as t→∞.
Assume a↦(t↦φ_t(a)) is continuous from A into C_b(T,B) with its supremum norm; this is
IsUniform φ. Let X be any topological space. The continuous map uniformC0Orbit φ
hφ:C₀(X,A)→C_b(T,C₀(X,B)) sends f to the time orbit with value F(f)(t)(x)=φ_t(f(x))-φ_t(0).
Both C₀ function spaces and the bounded-orbit space have their supremum norms.
-/
noncomputable def uniformC0Orbit {X : Type uX} [TopologicalSpace X]
    (φ : AsymptoticMorphism A B) (hφ : IsUniform φ) :
    C(C₀(X, A), AsymptoticTime →ᵇ C₀(X, B)) := by
  let hnormalized : IsUniform (AsymptoticMorphism.normalize φ) := IsUniform.normalize hφ
  let F : C(A, AsymptoticTime →ᵇ B) := Classical.choose hnormalized
  have hF : ∀ (t : AsymptoticTime) (a : A),
      F a t = AsymptoticMorphism.normalize φ t a :=
    Classical.choose_spec hnormalized
  have hzero : F 0 = 0 := by
    apply BoundedContinuousFunction.ext
    intro t
    change F 0 t = 0
    exact (hF t 0).trans (normalize_zero φ t)
  exact
    { toFun := fun f =>
        ZeroAtInftyContinuousMap.flipToBCF
          (ZeroAtInftyContinuousMap.postcomp F hzero f)
      continuous_toFun :=
        (ZeroAtInftyContinuousMap.isometry_flipToBCF
          (X := X) (T := AsymptoticTime) (B := B)).continuous.comp
          (ZeroAtInftyContinuousMap.continuous_postcomp
            (X := X) (A := A) (B := AsymptoticTime →ᵇ B) F hzero) }

/-- **Value of the uniform C₀ orbit map.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let φ be an asymptotic star morphism A→B, a family φ_t:A→B with continuous
time orbits and vanishing additive, complex-scalar, multiplicative and star defects as t→∞.
Assume a↦(t↦φ_t(a)) is continuous from A into C_b(T,B) with its supremum norm; this is
IsUniform φ. For any topological space X, f∈C₀(X,A), t≥1 and x∈X, uniformC0Orbit φ hφ f t
x=φ_t(f(x))-φ_t(0).
-/
@[simp]
theorem uniformC0Orbit_apply {X : Type uX} [TopologicalSpace X]
    (φ : AsymptoticMorphism A B) (hφ : IsUniform φ)
    (f : C₀(X, A)) (t : AsymptoticTime) (x : X) :
    uniformC0Orbit φ hφ f t x = AsymptoticMorphism.normalize φ t (f x) := by
  let hnormalized : IsUniform (AsymptoticMorphism.normalize φ) := IsUniform.normalize hφ
  let F : C(A, AsymptoticTime →ᵇ B) := Classical.choose hnormalized
  have hF : ∀ (s : AsymptoticTime) (a : A),
      F a s = AsymptoticMorphism.normalize φ s a :=
    Classical.choose_spec hnormalized
  have hzero : F 0 = 0 := by
    apply BoundedContinuousFunction.ext
    intro s
    change F 0 s = 0
    exact (hF s 0).trans (normalize_zero φ s)
  change ZeroAtInftyContinuousMap.flipToBCF
    (ZeroAtInftyContinuousMap.postcomp F hzero f) t x =
      AsymptoticMorphism.normalize φ t (f x)
  rw [ZeroAtInftyContinuousMap.flipToBCF_apply, ZeroAtInftyContinuousMap.postcomp_apply]
  exact hF t (f x)

/-- **Asymptotic morphism induced on C₀ functions.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let φ be an asymptotic star morphism A→B, a family φ_t:A→B with continuous
time orbits and vanishing additive, complex-scalar, multiplicative and star defects as t→∞.
Assume a↦(t↦φ_t(a)) is continuous from A into C_b(T,B) with its supremum norm; this is
IsUniform φ. For any topological space X, uniformC0Morphism φ hφ:C₀(X,A)→C₀(X,B) is the family
F_t(f)(x)=φ_t(f(x))-φ_t(0). Its time continuity and all four algebraic defect limits use the
supremum norm on C₀(X,B).
-/
noncomputable def uniformC0Morphism {X : Type uX} [TopologicalSpace X]
    (φ : AsymptoticMorphism A B) (hφ : IsUniform φ) :
    AsymptoticMorphism C₀(X, A) C₀(X, B) := by
  let hnormalized : IsUniform (AsymptoticMorphism.normalize φ) := IsUniform.normalize hφ
  let F : C(A, AsymptoticTime →ᵇ B) := Classical.choose hnormalized
  have hF : ∀ (t : AsymptoticTime) (a : A),
      F a t = AsymptoticMorphism.normalize φ t a :=
    Classical.choose_spec hnormalized
  have hOrbit (f : C₀(X, A)) (t : AsymptoticTime) (x : X) :
      uniformC0Orbit φ hφ f t x = F (f x) t :=
    (uniformC0Orbit_apply φ hφ f t x).trans ((hF t (f x)).symm)
  -- A proof-local adapter, not a new compact-convergence API. Its filter is arbitrary.
  have hlimit {Y : Type uA} [TopologicalSpace Y]
      (K : Set Y) (hK : IsCompact K) (D : C(Y, AsymptoticTime →ᵇ B))
      (r : X → K) (d : AsymptoticTime → C₀(X, B)) (L : Filter AsymptoticTime)
      (hvalue : ∀ (t : AsymptoticTime) (x : X), d t x = D (r x) t)
      (hpoint : ∀ y : K, Tendsto (fun t => D y t) L (nhds (0 : B))) :
      Tendsto d L (nhds (0 : C₀(X, B))) := by
    let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have hEqui : Equicontinuous (fun t (y : K) => D y t) := by
      apply equicontinuous_iff_continuous.mpr
      change Continuous (fun y : K =>
        UniformFun.ofFun (fun t : AsymptoticTime => D (y : Y) t))
      exact BoundedContinuousFunction.isInducing_coeFn.continuous.comp
        ((map_continuous D).comp continuous_subtype_val)
    have hPi : Tendsto (fun t (y : K) => D y t) L (nhds (fun _ : K => (0 : B))) :=
      tendsto_pi_nhds.mpr hpoint
    have hUniformFun :=
      (Equicontinuous.tendsto_uniformFun_iff_pi hEqui L
        (fun _ : K => (0 : B))).mpr hPi
    have hUniform : TendstoUniformly (fun t (y : K) => D y t)
        (fun _ : K => (0 : B)) L := by
      simpa only [Function.comp_def, UniformFun.toFun_ofFun] using
        UniformFun.tendsto_iff_tendstoUniformly.mp hUniformFun
    apply ZeroAtInftyContinuousMap.tendsto_iff_tendstoUniformly.mpr
    change TendstoUniformly (fun t x => d t x) (fun _ : X => (0 : B)) L
    have hvalues : (fun t x => d t x) = (fun t x => D (r x) t) :=
      funext fun t => funext (hvalue t)
    rw [hvalues]
    simpa only [Function.comp_def] using hUniform.comp r
  refine
    { toFun := fun t f => uniformC0Orbit φ hφ f t
      continuous_orbit := ?_
      add_defect_tendsto := ?_
      smul_defect_tendsto := ?_
      mul_defect_tendsto := ?_
      star_defect_tendsto := ?_ }
  · intro f
    exact map_continuous (uniformC0Orbit φ hφ f)
  · intro f g
    let K : Set (A × A) :=
      (insert 0 (Set.range f)) ×ˢ (insert 0 (Set.range g))
    have hK : IsCompact K :=
      ((zero_at_infty f).isCompact_insert_range_of_cocompact (map_continuous f)).prod
        ((zero_at_infty g).isCompact_insert_range_of_cocompact (map_continuous g))
    let D : C(A × A, AsymptoticTime →ᵇ B) :=
      { toFun := fun p => F (p.1 + p.2) - (F p.1 + F p.2)
        continuous_toFun :=
          ((map_continuous F).comp (continuous_fst.fun_add continuous_snd)).fun_sub
            (((map_continuous F).comp continuous_fst).fun_add
              ((map_continuous F).comp continuous_snd)) }
    let r : X → K := fun x =>
      ⟨(f x, g x), ⟨Set.mem_insert_of_mem 0 (Set.mem_range_self x),
        Set.mem_insert_of_mem 0 (Set.mem_range_self x)⟩⟩
    refine hlimit K hK D r
      (fun t => uniformC0Orbit φ hφ (f + g) t -
        (uniformC0Orbit φ hφ f t + uniformC0Orbit φ hφ g t)) atTop ?_ ?_
    · intro t x
      change (uniformC0Orbit φ hφ (f + g) t -
        (uniformC0Orbit φ hφ f t + uniformC0Orbit φ hφ g t)) x =
        (F (f x + g x) - (F (f x) + F (g x))) t
      simp only [ZeroAtInftyContinuousMap.sub_apply, ZeroAtInftyContinuousMap.add_apply,
        hOrbit, BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.add_apply]
    · intro p
      change Tendsto (fun t =>
        (F ((p : A × A).1 + (p : A × A).2) -
          (F ((p : A × A).1) + F ((p : A × A).2))) t) atTop (nhds (0 : B))
      simpa only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.add_apply,
        hF, toFun_eq_coe] using
        (AsymptoticMorphism.normalize φ).add_defect_tendsto
          (p : A × A).1 (p : A × A).2
  · intro z f
    let K : Set A := insert 0 (Set.range f)
    have hK : IsCompact K :=
      (zero_at_infty f).isCompact_insert_range_of_cocompact (map_continuous f)
    let D : C(A, AsymptoticTime →ᵇ B) :=
      { toFun := fun a => F (z • a) - z • F a
        continuous_toFun :=
          ((map_continuous F).comp (continuous_id.fun_const_smul z)).fun_sub
            ((map_continuous F).fun_const_smul z) }
    let r : X → K := fun x => ⟨f x, Set.mem_insert_of_mem 0 (Set.mem_range_self x)⟩
    refine hlimit K hK D r
      (fun t => uniformC0Orbit φ hφ (z • f) t - z • uniformC0Orbit φ hφ f t)
      atTop ?_ ?_
    · intro t x
      change (uniformC0Orbit φ hφ (z • f) t - z • uniformC0Orbit φ hφ f t) x =
        (F (z • f x) - z • F (f x)) t
      simp only [ZeroAtInftyContinuousMap.sub_apply, ZeroAtInftyContinuousMap.smul_apply,
        hOrbit, BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.smul_apply]
    · intro a
      change Tendsto (fun t => (F (z • (a : A)) - z • F (a : A)) t)
        atTop (nhds (0 : B))
      simpa only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.smul_apply,
        hF, toFun_eq_coe] using
        (AsymptoticMorphism.normalize φ).smul_defect_tendsto z (a : A)
  · intro f g
    let K : Set (A × A) :=
      (insert 0 (Set.range f)) ×ˢ (insert 0 (Set.range g))
    have hK : IsCompact K :=
      ((zero_at_infty f).isCompact_insert_range_of_cocompact (map_continuous f)).prod
        ((zero_at_infty g).isCompact_insert_range_of_cocompact (map_continuous g))
    let D : C(A × A, AsymptoticTime →ᵇ B) :=
      { toFun := fun p => F (p.1 * p.2) - F p.1 * F p.2
        continuous_toFun :=
          ((map_continuous F).comp (continuous_fst.fun_mul continuous_snd)).fun_sub
            (((map_continuous F).comp continuous_fst).fun_mul
              ((map_continuous F).comp continuous_snd)) }
    let r : X → K := fun x =>
      ⟨(f x, g x), ⟨Set.mem_insert_of_mem 0 (Set.mem_range_self x),
        Set.mem_insert_of_mem 0 (Set.mem_range_self x)⟩⟩
    refine hlimit K hK D r
      (fun t => uniformC0Orbit φ hφ (f * g) t -
        uniformC0Orbit φ hφ f t * uniformC0Orbit φ hφ g t) atTop ?_ ?_
    · intro t x
      change (uniformC0Orbit φ hφ (f * g) t -
        uniformC0Orbit φ hφ f t * uniformC0Orbit φ hφ g t) x =
        (F (f x * g x) - F (f x) * F (g x)) t
      simp only [ZeroAtInftyContinuousMap.sub_apply, ZeroAtInftyContinuousMap.mul_apply,
        hOrbit, BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.mul_apply]
    · intro p
      change Tendsto (fun t =>
        (F ((p : A × A).1 * (p : A × A).2) -
          F ((p : A × A).1) * F ((p : A × A).2)) t) atTop (nhds (0 : B))
      simpa only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.mul_apply,
        hF, toFun_eq_coe] using
        (AsymptoticMorphism.normalize φ).mul_defect_tendsto
          (p : A × A).1 (p : A × A).2
  · intro f
    let K : Set A := insert 0 (Set.range f)
    have hK : IsCompact K :=
      (zero_at_infty f).isCompact_insert_range_of_cocompact (map_continuous f)
    let D : C(A, AsymptoticTime →ᵇ B) :=
      { toFun := fun a => F (star a) - star (F a)
        continuous_toFun :=
          ((map_continuous F).comp continuous_star).fun_sub (map_continuous F).star }
    let r : X → K := fun x => ⟨f x, Set.mem_insert_of_mem 0 (Set.mem_range_self x)⟩
    refine hlimit K hK D r
      (fun t => uniformC0Orbit φ hφ (star f) t - star (uniformC0Orbit φ hφ f t))
      atTop ?_ ?_
    · intro t x
      change (uniformC0Orbit φ hφ (star f) t - star (uniformC0Orbit φ hφ f t)) x =
        (F (star (f x)) - star (F (f x))) t
      simp only [ZeroAtInftyContinuousMap.sub_apply, ZeroAtInftyContinuousMap.star_apply,
        hOrbit, BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.star_apply]
    · intro a
      change Tendsto (fun t => (F (star (a : A)) - star (F (a : A))) t)
        atTop (nhds (0 : B))
      simpa only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.star_apply,
        hF, toFun_eq_coe] using
        (AsymptoticMorphism.normalize φ).star_defect_tendsto (a : A)

/-- **Value of the induced C₀ asymptotic family.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let φ be an asymptotic star morphism A→B, a family φ_t:A→B with continuous
time orbits and vanishing additive, complex-scalar, multiplicative and star defects as t→∞.
Assume a↦(t↦φ_t(a)) is continuous from A into C_b(T,B) with its supremum norm; this is
IsUniform φ. For any topological space X, f∈C₀(X,A), t≥1 and x∈X, uniformC0Morphism φ hφ t f
x=φ_t(f(x))-φ_t(0).
-/
@[simp]
theorem uniformC0Morphism_apply {X : Type uX} [TopologicalSpace X]
    (φ : AsymptoticMorphism A B) (hφ : IsUniform φ)
    (t : AsymptoticTime) (f : C₀(X, A)) (x : X) :
    uniformC0Morphism φ hφ t f x = AsymptoticMorphism.normalize φ t (f x) := by
  change uniformC0Orbit φ hφ f t x = AsymptoticMorphism.normalize φ t (f x)
  exact uniformC0Orbit_apply φ hφ f t x

/-- **Uniformity of the induced C₀ asymptotic morphism.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let φ be an asymptotic star morphism A→B, a family φ_t:A→B with continuous
time orbits and vanishing additive, complex-scalar, multiplicative and star defects as t→∞.
Assume a↦(t↦φ_t(a)) is continuous from A into C_b(T,B) with its supremum norm; this is
IsUniform φ. For any topological space X, the family F=uniformC0Morphism φ hφ satisfies
IsUniform F: f↦(t↦F_t(f)) is continuous C₀(X,A)→C_b(T,C₀(X,B)) in the supremum norms.
-/
theorem isUniform_uniformC0Morphism {X : Type uX} [TopologicalSpace X]
    (φ : AsymptoticMorphism A B) (hφ : IsUniform φ) :
    IsUniform (uniformC0Morphism (X := X) φ hφ) := by
  refine ⟨uniformC0Orbit φ hφ, ?_⟩
  intro t f
  rfl

end AsymptoticMorphism
