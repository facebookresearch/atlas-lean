/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.RingTheory.Length
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Exact.Basic

/-!
# Cokernel length of a composite with an injective second map

Let R be a ring, f:M→N and g:N→P linear maps of left R-modules, and write coker(f)=N/range(f)
with length ℓ_R in ℕ∪{∞}. If g is injective, 0→coker(f)→coker(gf)→coker(g)→0 is exact, so
ℓ_R(coker(gf))=ℓ_R(coker f)+ℓ_R(coker g), including infinite lengths.
-/

@[expose] public section
noncomputable section

universe u v w z

namespace LinearMap

variable {R : Type u} [Ring R]
variable {M : Type v} {N : Type w} {P : Type z}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [Module R M] [Module R N] [Module R P]

private def cokerCompLeft (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    N ⧸ f.range →ₗ[R] P ⧸ (g.comp f).range :=
  f.range.mapQ (g.comp f).range g (by
    rintro n ⟨m, rfl⟩
    exact ⟨m, rfl⟩)

private def cokerCompRight (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    P ⧸ (g.comp f).range →ₗ[R] P ⧸ g.range :=
  (g.comp f).range.mapQ g.range LinearMap.id (by
    rintro p ⟨m, rfl⟩
    exact ⟨f m, rfl⟩)

/-- **Additivity of full cokernel lengths under an injective second map.**

Let R be a ring, f:M→N and g:N→P linear maps of left R-modules, and write coker(f)=N/range(f)
with length ℓ_R in ℕ∪{∞}. For injective g, ℓ_R(P/range(gf))=ℓ_R(N/range f)+ℓ_R(P/range g).
-/
theorem length_coker_comp_of_injective (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hg : Function.Injective g) :
    Module.length R (P ⧸ (g.comp f).range) =
      Module.length R (N ⧸ f.range) + Module.length R (P ⧸ g.range) := by
  let i := cokerCompLeft f g
  let j := cokerCompRight f g
  have hi : Function.Injective i := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective f.range q
    change (g.comp f).range.mkQ (g n) = 0 at hq
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hq
    obtain ⟨m, hm⟩ := hq
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨m, hg hm⟩
  have hj : Function.Surjective j := by
    intro q
    obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective g.range q
    exact ⟨(g.comp f).range.mkQ p, rfl⟩
  have hseq : Function.Exact i j := by
    intro q
    obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective (g.comp f).range q
    constructor
    · intro hp
      change g.range.mkQ p = 0 at hp
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hp
      obtain ⟨n, hn⟩ := hp
      refine ⟨f.range.mkQ n, ?_⟩
      change (g.comp f).range.mkQ (g n) = (g.comp f).range.mkQ p
      rw [hn]
    · rintro ⟨q, hq⟩
      rw [← hq]
      obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective f.range q
      change g.range.mkQ (g n) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨n, rfl⟩
  exact Module.length_eq_add_of_exact i j hi hj hseq

private def upperBlockMap (f : M →ₗ[R] M) (r : N →ₗ[R] M) (g : N →ₗ[R] N) :
    M × N →ₗ[R] M × N :=
  (f.comp (LinearMap.fst R M N) + r.comp (LinearMap.snd R M N)).prod
    (g.comp (LinearMap.snd R M N))

/-- **Cokernel length of an upper block map.**

Let R be a ring, M,N R-modules, f:M→M, r:N→M and injective g:N→N linear. The map
T(x,y)=(f(x)+r(y),g(y)) has ℓ_R(coker T)=ℓ_R(coker f)+ℓ_R(coker g), with no finite-length
hypothesis.
-/
theorem length_coker_upper_block_of_injective
    (f : M →ₗ[R] M) (r : N →ₗ[R] M) (g : N →ₗ[R] N) (hg : Function.Injective g) :
    Module.length R ((M × N) ⧸
        ((f.comp (LinearMap.fst R M N) + r.comp (LinearMap.snd R M N)).prod
          (g.comp (LinearMap.snd R M N))).range) =
      Module.length R (M ⧸ f.range) + Module.length R (N ⧸ g.range) := by
  let T := upperBlockMap f r g
  let i : M ⧸ f.range →ₗ[R] (M × N) ⧸ T.range :=
    f.range.mapQ T.range (LinearMap.inl R M N) (by
      rintro m ⟨a, rfl⟩
      refine ⟨(a, 0), ?_⟩
      change (f a + r 0, g 0) = (f a, 0)
      rw [map_zero, map_zero, add_zero])
  let j : (M × N) ⧸ T.range →ₗ[R] N ⧸ g.range :=
    T.range.mapQ g.range (LinearMap.snd R M N) (by
      rintro p ⟨q, rfl⟩
      exact ⟨q.2, rfl⟩)
  have hi : Function.Injective i := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective f.range q
    change T.range.mkQ (m, 0) = 0 at hq
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hq
    obtain ⟨⟨a, b⟩, hab⟩ := hq
    have hb0 : g b = 0 := congrArg Prod.snd hab
    have hb : b = 0 := hg (hb0.trans g.map_zero.symm)
    have ha : f a + r b = m := congrArg Prod.fst hab
    rw [hb, map_zero, add_zero] at ha
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨a, ha⟩
  have hj : Function.Surjective j := by
    intro q
    obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective g.range q
    exact ⟨T.range.mkQ (0, n), rfl⟩
  have hseq : Function.Exact i j := by
    intro q
    obtain ⟨⟨m, n⟩, rfl⟩ := Submodule.mkQ_surjective T.range q
    constructor
    · intro hn
      change g.range.mkQ n = 0 at hn
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hn
      obtain ⟨b, hb⟩ := hn
      refine ⟨f.range.mkQ (m - r b), ?_⟩
      change T.range.mkQ (m - r b, 0) = T.range.mkQ (m, n)
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      refine ⟨(0, -b), ?_⟩
      change (f 0 + r (-b), g (-b)) = (m - r b, 0) - (m, n)
      ext <;> simp [hb]
    · rintro ⟨q, hq⟩
      rw [← hq]
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective f.range q
      change g.range.mkQ 0 = 0
      exact map_zero _
  exact Module.length_eq_add_of_exact i j hi hj hseq

/-- **Domain equivalence preserves cokernel length.**

Let R be a ring, f:M→N and g:N→P linear maps of left R-modules, and write coker(f)=N/range(f)
with length ℓ_R in ℕ∪{∞}. For a linear equivalence e:Q≃M, ℓ_R(N/range(f∘e))=ℓ_R(N/range f).
-/
theorem length_coker_precompose_equiv (f : M →ₗ[R] N) (e : P ≃ₗ[R] M) :
    Module.length R (N ⧸ (f.comp e.toLinearMap).range) = Module.length R (N ⧸ f.range) := by
  have hr : (f.comp e.toLinearMap).range = f.range := by
    ext n
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨e p, rfl⟩
    · rintro ⟨m, rfl⟩
      exact ⟨e.symm m, by simp⟩
  exact congrArg (fun Q : Submodule R N => Module.length R (N ⧸ Q)) hr

/-- **Codomain equivalence preserves cokernel length.**

Let R be a ring, f:M→N and g:N→P linear maps of left R-modules, and write coker(f)=N/range(f)
with length ℓ_R in ℕ∪{∞}. For a linear equivalence e:N≃Q, ℓ_R(Q/range(e∘f))=ℓ_R(N/range f).
-/
theorem length_coker_postcompose_equiv (f : M →ₗ[R] N) (e : N ≃ₗ[R] P) :
    Module.length R (P ⧸ (e.toLinearMap.comp f).range) = Module.length R (N ⧸ f.range) := by
  have hz : Module.length R (P ⧸ e.toLinearMap.range) = 0 := by
    rw [LinearMap.range_eq_top.mpr e.surjective]
    exact Module.length_eq_zero
  have h := length_coker_comp_of_injective f e.toLinearMap e.injective
  rw [hz, add_zero] at h
  exact h

end LinearMap
