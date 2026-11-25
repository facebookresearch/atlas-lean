/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Algebra.Group.Commutator

/-! # Stable Steinberg group via generators and relations

The stable Steinberg group `St(R)` is presented by generators `x_{ij}(a)`
with `i j : ℕ`, `i ≠ j`, `a : R`, and relations

* `x_{ij}(a) x_{ij}(b) = x_{ij}(a + b)`,
* `[x_{ij}(a), x_{kl}(b)] = 1` when `i ≠ l` and `j ≠ k`,
* `[x_{ij}(a), x_{jk}(b)] = x_{ik}(a * b)` for pairwise distinct `i, j, k`,

with commutator `x y x⁻¹ y⁻¹` and noncommutative order `a * b`.
The presentation is on `ℕ` directly and functorial via `PresentedGroup.map`.
-/

@[expose] public section

namespace AlgebraicKTheory

universe u

open scoped commutatorElement

/-- Stable Steinberg generator `x_{ij}(a)` with `i ≠ j`. -/
structure SteinbergGenerator (R : Type u) where
  i : ℕ
  j : ℕ
  hij : i ≠ j
  a : R

namespace SteinbergGenerator

/-- Nonunital coefficient map on Steinberg generators. -/
def mapNonUnital {R S : Type u} [Ring R] [Ring S] (f : R →ₙ+* S)
    (g : SteinbergGenerator R) : SteinbergGenerator S :=
  ⟨g.i, g.j, g.hij, f g.a⟩

/-- A nonunital identity map fixes every Steinberg generator. -/
@[simp]
theorem mapNonUnital_id {R : Type u} [Ring R] (g : SteinbergGenerator R) :
    mapNonUnital (NonUnitalRingHom.id R) g = g := by
  cases g
  rfl

/-- Nonunital coefficient maps compose on Steinberg generators. -/
@[simp]
theorem mapNonUnital_comp {R S T : Type u} [Ring R] [Ring S] [Ring T]
    (f : R →ₙ+* S) (g : S →ₙ+* T) (x : SteinbergGenerator R) :
    mapNonUnital (g.comp f) x = mapNonUnital g (mapNonUnital f x) := by
  cases x
  rfl

/-- Coefficient map on Steinberg generators. -/
def map {R S : Type u} [Ring R] [Ring S] (f : R →+* S) (g : SteinbergGenerator R) :
    SteinbergGenerator S :=
  mapNonUnital f.toNonUnitalRingHom g

@[simp]
theorem map_id {R : Type u} [Ring R] (g : SteinbergGenerator R) :
    map (RingHom.id R) g = g := by
  cases g
  rfl

@[simp]
theorem map_comp {R S T : Type u} [Ring R] [Ring S] [Ring T]
    (f : R →+* S) (g : S →+* T) (x : SteinbergGenerator R) :
    map (g.comp f) x = map g (map f x) := by
  cases x
  rfl

/-- Free generator `x_{ij}(a)` as an element of the free group. -/
def free {R : Type u} (i j : ℕ) (hij : i ≠ j) (a : R) :
    FreeGroup (SteinbergGenerator R) :=
  FreeGroup.of ⟨i, j, hij, a⟩

end SteinbergGenerator

/-- Additive relation `x_{ij}(a) x_{ij}(b) = x_{ij}(a + b)`. -/
def steinbergAddRel (R : Type u) [Ring R] :
    Set (FreeGroup (SteinbergGenerator R)) :=
  { r |
    ∃ (i j : ℕ) (hij : i ≠ j) (a b : R),
      r = SteinbergGenerator.free i j hij a *
        SteinbergGenerator.free i j hij b *
          (SteinbergGenerator.free i j hij (a + b))⁻¹ }

/-- Distant commutator relation `[x_{ij}(a), x_{kl}(b)] = 1` when `i ≠ l` and `j ≠ k`. -/
def steinbergCommRel (R : Type u) [Ring R] :
    Set (FreeGroup (SteinbergGenerator R)) :=
  { r |
    ∃ (i j k l : ℕ) (hij : i ≠ j) (hkl : k ≠ l) (_hil : i ≠ l) (_hjk : j ≠ k)
        (a : R) (b : R),
      r = ⁅SteinbergGenerator.free (R := R) i j hij a,
          SteinbergGenerator.free k l hkl b⁆ }

/-- Chevalley relation `[x_{ij}(a), x_{jk}(b)] = x_{ik}(a * b)` for distinct `i, j, k`. -/
def steinbergChevRel (R : Type u) [Ring R] :
    Set (FreeGroup (SteinbergGenerator R)) :=
  { r |
    ∃ (i j k : ℕ) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R),
      r = ⁅SteinbergGenerator.free (R := R) i j hij a,
            SteinbergGenerator.free j k hjk b⁆ *
          (SteinbergGenerator.free i k hik (a * b))⁻¹ }

/-- Stable Steinberg relation set as union of the three families. -/
def steinbergRelations (R : Type u) [Ring R] :
    Set (FreeGroup (SteinbergGenerator R)) :=
  steinbergAddRel R ∪ steinbergCommRel R ∪ steinbergChevRel R

/-- Stable Steinberg group `St(R)` presented on `ℕ`. -/
abbrev StableSteinberg (R : Type u) [Ring R] : Type u :=
  PresentedGroup (steinbergRelations R)

namespace StableSteinberg

/-- Generator `x_{ij}(a)` in `St(R)`. -/
def x {R : Type u} [Ring R] (i j : ℕ) (hij : i ≠ j) (a : R) :
    StableSteinberg R :=
  PresentedGroup.of ⟨i, j, hij, a⟩

/-- Additive law `x_{ij}(a) x_{ij}(b) = x_{ij}(a + b)` in `St(R)`. -/
theorem x_add {R : Type u} [Ring R] (i j : ℕ) (hij : i ≠ j) (a b : R) :
    (x (R := R) i j hij a) * x i j hij b = x i j hij (a + b) := by
  have hmem :
      SteinbergGenerator.free (R := R) i j hij a *
        SteinbergGenerator.free i j hij b *
          (SteinbergGenerator.free i j hij (a + b))⁻¹ ∈
        steinbergRelations (R := R) := by
    simp only [steinbergRelations, Set.mem_union]
    left
    left
    exact ⟨i, j, hij, a, b, rfl⟩
  have h_eq :
      PresentedGroup.mk (steinbergRelations R)
          (SteinbergGenerator.free i j hij a *
            SteinbergGenerator.free i j hij b) =
        PresentedGroup.mk (steinbergRelations R)
          (SteinbergGenerator.free i j hij (a + b)) := by
    apply PresentedGroup.mk_eq_mk_of_mul_inv_mem
    simpa using hmem
  have hx : (x (R := R) i j hij a) =
      PresentedGroup.mk (steinbergRelations R)
        (SteinbergGenerator.free i j hij a) := by
    rfl
  have hy : (x (R := R) i j hij b) =
      PresentedGroup.mk (steinbergRelations R)
        (SteinbergGenerator.free i j hij b) := by
    rfl
  have hz : (x (R := R) i j hij (a + b)) =
      PresentedGroup.mk (steinbergRelations R)
        (SteinbergGenerator.free i j hij (a + b)) := by
    rfl
  calc
    x (R := R) i j hij a * x i j hij b
        = PresentedGroup.mk (steinbergRelations R)
            (SteinbergGenerator.free i j hij a) *
          PresentedGroup.mk (steinbergRelations R)
            (SteinbergGenerator.free i j hij b) := by
        rw [← hx, ← hy]
    _ = PresentedGroup.mk (steinbergRelations R)
          (SteinbergGenerator.free i j hij a *
            SteinbergGenerator.free i j hij b) := by
        rw [← MonoidHom.map_mul]
    _ = PresentedGroup.mk (steinbergRelations R)
          (SteinbergGenerator.free i j hij (a + b)) := h_eq
    _ = x i j hij (a + b) := hz.symm

/-- For a unital ring `R`, `a, b : R`, and natural-number indices `i, j, k, l`
with `i ≠ j`, `k ≠ l`, `i ≠ l`, and `j ≠ k`, the commutator
`[x_{ij}(a), x_{kl}(b)]` is `1` in `St(R)`. The convention is
`[x, y] = x * y * x⁻¹ * y⁻¹`. -/
theorem x_comm {R : Type u} [Ring R] (i j k l : ℕ) (hij : i ≠ j) (hkl : k ≠ l)
    (hil : i ≠ l) (hjk : j ≠ k) (a : R) (b : R) :
    ⁅x (R := R) i j hij a, x k l hkl b⁆ = (1 : StableSteinberg R) := by
  have hmem :
      (⁅SteinbergGenerator.free (R := R) i j hij a,
          SteinbergGenerator.free k l hkl b⁆ : FreeGroup (SteinbergGenerator R)) ∈
        steinbergRelations (R := R) := by
    simp only [steinbergRelations, Set.mem_union]
    left
    right
    exact ⟨i, j, k, l, hij, hkl, hil, hjk, a, b, rfl⟩
  have h_one :
      PresentedGroup.mk (steinbergRelations R)
          (⁅SteinbergGenerator.free (R := R) i j hij a,
              SteinbergGenerator.free k l hkl b⁆) = 1 :=
    PresentedGroup.one_of_mem (by simpa using hmem)
  have hx :
      (x (R := R) i j hij a) =
        PresentedGroup.mk (steinbergRelations R)
          (SteinbergGenerator.free i j hij a) := by
    rfl
  have hy :
      (x (R := R) k l hkl b) =
        PresentedGroup.mk (steinbergRelations R)
          (SteinbergGenerator.free k l hkl b) := by
    rfl
  calc
    ⁅x (R := R) i j hij a, x k l hkl b⁆
        = ⁅PresentedGroup.mk (steinbergRelations R)
              (SteinbergGenerator.free i j hij a),
            PresentedGroup.mk (steinbergRelations R)
              (SteinbergGenerator.free k l hkl b)⁆ := by
        rw [← hx, ← hy]
    _ = PresentedGroup.mk (steinbergRelations R)
          (⁅SteinbergGenerator.free (R := R) i j hij a,
              SteinbergGenerator.free k l hkl b⁆) := by
        simp [commutatorElement_def]
    _ = 1 := h_one

/-- For a unital ring `R`, `a, b : R`, and pairwise distinct natural-number
indices `i, j, k`, the Chevalley relation in `St(R)` is
`[x_{ij}(a), x_{jk}(b)] = x_{ik}(a * b)`. The coefficient multiplies
`a` by `b` in that order, with `[x, y] = x * y * x⁻¹ * y⁻¹`. -/
theorem x_chev {R : Type u} [Ring R] (i j k : ℕ) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b : R) :
    ⁅x (R := R) i j hij a, x j k hjk b⁆ = x i k hik (a * b) := by
  have hmem :
      (⁅SteinbergGenerator.free (R := R) i j hij a,
            SteinbergGenerator.free j k hjk b⁆ *
          (SteinbergGenerator.free i k hik (a * b))⁻¹ :
          FreeGroup (SteinbergGenerator R)) ∈
        steinbergRelations (R := R) := by
    simp only [steinbergRelations, Set.mem_union]
    right
    exact ⟨i, j, k, hij, hjk, hik, a, b, rfl⟩
  have h_eq :
      PresentedGroup.mk (steinbergRelations R)
          (⁅SteinbergGenerator.free (R := R) i j hij a,
              SteinbergGenerator.free j k hjk b⁆) =
        PresentedGroup.mk (steinbergRelations R)
          (SteinbergGenerator.free i k hik (a * b)) := by
    apply PresentedGroup.mk_eq_mk_of_mul_inv_mem
    simpa using hmem
  have hx :
      (x (R := R) i j hij a) =
        PresentedGroup.mk (steinbergRelations R)
          (SteinbergGenerator.free i j hij a) := by
    rfl
  have hy :
      (x (R := R) j k hjk b) =
        PresentedGroup.mk (steinbergRelations R)
          (SteinbergGenerator.free j k hjk b) := by
    rfl
  have hz :
      (x (R := R) i k hik (a * b)) =
        PresentedGroup.mk (steinbergRelations R)
          (SteinbergGenerator.free i k hik (a * b)) := by
    rfl
  calc
    ⁅x (R := R) i j hij a, x j k hjk b⁆
        = ⁅PresentedGroup.mk (steinbergRelations R)
              (SteinbergGenerator.free i j hij a),
            PresentedGroup.mk (steinbergRelations R)
              (SteinbergGenerator.free j k hjk b)⁆ := by
        rw [← hx, ← hy]
    _ = PresentedGroup.mk (steinbergRelations R)
          (⁅SteinbergGenerator.free (R := R) i j hij a,
              SteinbergGenerator.free j k hjk b⁆) := by
        simp [commutatorElement_def]
    _ = PresentedGroup.mk (steinbergRelations R)
          (SteinbergGenerator.free i k hik (a * b)) := h_eq
    _ = x i k hik (a * b) := hz.symm

/-- For unital rings `R` and `S` in the same universe, a map `f : R →ₙ+* S`
induces the group homomorphism `St(R) →* St(S)` sending each generator
`x_{ij}(a)` with `i ≠ j` to `x_{ij}(f(a))`. The coefficient map preserves
addition and multiplication but is not required to preserve `1`. -/
def mapNonUnitalRingHom {R S : Type u} [Ring R] [Ring S] (f : R →ₙ+* S) :
    StableSteinberg R →* StableSteinberg S :=
  PresentedGroup.map (FreeGroup.map (SteinbergGenerator.mapNonUnital f)) (by
    intro r hr
    simp only [steinbergRelations, Set.mem_union] at hr ⊢
    rcases hr with (hr | hr) | hr
    · left
      left
      obtain ⟨i, j, hij, a, b, rfl⟩ := hr
      simp only [SteinbergGenerator.free, FreeGroup.map.of, SteinbergGenerator.mapNonUnital,
        map_mul, map_inv, map_add]
      exact ⟨i, j, hij, f a, f b, rfl⟩
    · left
      right
      obtain ⟨i, j, k, l, hij, hkl, _hil, _hjk, a, b, rfl⟩ := hr
      have h_map_comm :
          FreeGroup.map (SteinbergGenerator.mapNonUnital f)
              (⁅SteinbergGenerator.free (R := R) i j hij a,
                  SteinbergGenerator.free k l hkl b⁆) =
            ⁅SteinbergGenerator.free (R := S) i j hij (f a),
                SteinbergGenerator.free k l hkl (f b)⁆ := by
        simp [SteinbergGenerator.free, FreeGroup.map.of, SteinbergGenerator.mapNonUnital,
          commutatorElement_def, map_mul, map_inv]
      rw [h_map_comm]
      exact ⟨i, j, k, l, hij, hkl, _hil, _hjk, f a, f b, rfl⟩
    · right
      obtain ⟨i, j, k, hij, hjk, hik, a, b, rfl⟩ := hr
      have h_mul : f (a * b) = f a * f b := map_mul f a b
      have h1 :
          FreeGroup.map (SteinbergGenerator.mapNonUnital f)
              (⁅SteinbergGenerator.free (R := R) i j hij a,
                    SteinbergGenerator.free j k hjk b⁆ *
                (SteinbergGenerator.free i k hik (a * b))⁻¹) =
            ⁅SteinbergGenerator.free (R := S) i j hij (f a),
                  SteinbergGenerator.free j k hjk (f b)⁆ *
              (SteinbergGenerator.free i k hik (f a * f b))⁻¹ := by
        simp [SteinbergGenerator.free, FreeGroup.map.of, SteinbergGenerator.mapNonUnital,
          commutatorElement_def, map_mul, map_inv, h_mul]
      rw [h1]
      exact ⟨i, j, k, hij, hjk, hik, f a, f b, rfl⟩)

@[simp]
theorem mapNonUnitalRingHom_x {R S : Type u} [Ring R] [Ring S] (f : R →ₙ+* S)
    (i j : ℕ) (hij : i ≠ j) (a : R) :
    mapNonUnitalRingHom (R := R) (S := S) f (x i j hij a) = x i j hij (f a) := by
  unfold x mapNonUnitalRingHom
  change QuotientGroup.map _ _ (FreeGroup.map (SteinbergGenerator.mapNonUnital f)) _
      (QuotientGroup.mk _) = QuotientGroup.mk _
  rw [QuotientGroup.map_mk]
  simp [FreeGroup.map.of, SteinbergGenerator.mapNonUnital]

@[simp]
theorem mapNonUnitalRingHom_id {R : Type u} [Ring R] :
    mapNonUnitalRingHom (R := R) (NonUnitalRingHom.id R) =
      MonoidHom.id (StableSteinberg R) := by
  apply PresentedGroup.ext
  intro g
  cases g with
  | mk i j hij a =>
    change mapNonUnitalRingHom (NonUnitalRingHom.id R) (x i j hij a) = x i j hij a
    simp

theorem mapNonUnitalRingHom_comp {R S T : Type u} [Ring R] [Ring S] [Ring T]
    (f : R →ₙ+* S) (g : S →ₙ+* T) :
    mapNonUnitalRingHom (g.comp f) =
      (mapNonUnitalRingHom g).comp (mapNonUnitalRingHom f) := by
  apply PresentedGroup.ext
  intro gr
  cases gr with
  | mk i j hij a =>
    change mapNonUnitalRingHom (g.comp f) (x i j hij a) =
      mapNonUnitalRingHom g (mapNonUnitalRingHom f (x i j hij a))
    simp

/-- Functorial map `St(R) →* St(S)` induced by a unital ring homomorphism. -/
def mapRingHom {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    StableSteinberg R →* StableSteinberg S :=
  mapNonUnitalRingHom f.toNonUnitalRingHom

@[simp]
theorem mapRingHom_x {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (i j : ℕ) (hij : i ≠ j) (a : R) :
    mapRingHom (R := R) (S := S) f (x i j hij a) = x i j hij (f a) := by
  exact mapNonUnitalRingHom_x f.toNonUnitalRingHom i j hij a

@[simp]
theorem mapRingHom_id {R : Type u} [Ring R] :
    mapRingHom (R := R) (RingHom.id R) = MonoidHom.id (StableSteinberg R) := by
  apply PresentedGroup.ext
  intro g
  cases g with
  | mk i j hij a =>
    change mapRingHom (RingHom.id R) (x i j hij a) = x i j hij a
    simp [mapRingHom_x]

theorem mapRingHom_comp {R S T : Type u} [Ring R] [Ring S] [Ring T]
    (f : R →+* S) (g : S →+* T) :
    mapRingHom (g.comp f) = (mapRingHom g).comp (mapRingHom f) := by
  apply PresentedGroup.ext
  intro gr
  cases gr with
  | mk i j hij a =>
    change mapRingHom (g.comp f) (x i j hij a) = mapRingHom g (mapRingHom f (x i j hij a))
    simp [mapRingHom_x, RingHom.comp_apply]

end StableSteinberg

end AlgebraicKTheory

end
