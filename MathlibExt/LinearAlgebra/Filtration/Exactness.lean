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

public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Exactness by finite descent in an increasing module filtration

The maps on adjacent filtration quotients are constructed from the original
linear maps. A boundary in a quotient lifts to an original element whose
error lies one stage lower. Induction on the finite stage gives exactness of
the original sequence.

This general transfer theorem has an associated-graded exactness premise.
Applying it to a concrete complex requires proving that premise for its
constructed quotient maps; it does not itself prove CE or PBW exactness.
-/

@[expose] public section

universe u v w t

variable {R : Type u} [Ring R]

namespace Submodule

variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The original lower filtration stage as a submodule of the upper stage. -/
def filtrationLower (F : ℕ → Submodule R M) (p : ℕ) : Submodule R (F (p + 1)) :=
  (F p).comap (F (p + 1)).subtype

/-- An adjacent quotient in an increasing filtration, retaining the original
upper-stage carrier and quotient map. -/
abbrev FiltrationLayer (F : ℕ → Submodule R M) (p : ℕ) :=
  F (p + 1) ⧸ filtrationLower F p

end Submodule

namespace LinearMap

variable {A : Type v} [AddCommGroup A] [Module R A]
  {B : Type w} [AddCommGroup B] [Module R B]
  {C : Type t} [AddCommGroup C] [Module R C]

/-- The actual restriction of a filtration-preserving map to a stage. -/
def filtrationStage (f : A →ₗ[R] B)
    (F : ℕ → Submodule R A) (G : ℕ → Submodule R B)
    (hf : ∀ p, ∀ x ∈ F p, f x ∈ G p) (p : ℕ) : F p →ₗ[R] G p where
  toFun x := ⟨f x, hf p x x.property⟩
  map_add' x y := by
    apply Subtype.ext
    exact f.map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact f.map_smul r x

@[simp]
theorem filtrationStage_apply (f : A →ₗ[R] B)
    (F : ℕ → Submodule R A) (G : ℕ → Submodule R B)
    (hf : ∀ p, ∀ x ∈ F p, f x ∈ G p) (p : ℕ) (x : F p) :
    (f.filtrationStage F G hf p x).val = f x.val := rfl

/-- The induced map on the original adjacent filtration quotients. -/
def filtrationLayerMap (f : A →ₗ[R] B)
    (F : ℕ → Submodule R A) (G : ℕ → Submodule R B)
    (hf : ∀ p, ∀ x ∈ F p, f x ∈ G p) (p : ℕ) :
    Submodule.FiltrationLayer F p →ₗ[R] Submodule.FiltrationLayer G p :=
  Submodule.mapQ (Submodule.filtrationLower F p) (Submodule.filtrationLower G p)
    (f.filtrationStage F G hf (p + 1)) (by
      intro x hx
      exact hf p x.val hx)

@[simp]
theorem filtrationLayerMap_mkQ (f : A →ₗ[R] B)
    (F : ℕ → Submodule R A) (G : ℕ → Submodule R B)
    (hf : ∀ p, ∀ x ∈ F p, f x ∈ G p) (p : ℕ) (x : F (p + 1)) :
    f.filtrationLayerMap F G hf p (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f.filtrationStage F G hf (p + 1) x) := rfl

/-- Exactness of the constructed quotient sequence supplies a genuine lift
whose error in the original module is one filtration stage lower. -/
theorem exists_boundary_mod_filtration
    (e : A →ₗ[R] B) (d : B →ₗ[R] C)
    (P : ℕ → Submodule R A) (F : ℕ → Submodule R B) (H : ℕ → Submodule R C)
    (he : ∀ p, ∀ x ∈ P p, e x ∈ F p)
    (hd : ∀ p, ∀ x ∈ F p, d x ∈ H p)
    (p : ℕ)
    (hgr : LinearMap.range (e.filtrationLayerMap P F he p) =
      LinearMap.ker (d.filtrationLayerMap F H hd p))
    (z : B) (hzF : z ∈ F (p + 1)) (hz : d z = 0) :
    ∃ y : A, y ∈ P (p + 1) ∧ z - e y ∈ F p := by
  let zF : F (p + 1) := ⟨z, hzF⟩
  let qz : Submodule.FiltrationLayer F p := (Submodule.filtrationLower F p).mkQ zF
  have hqz : d.filtrationLayerMap F H hd p qz = 0 := by
    change d.filtrationLayerMap F H hd p (Submodule.Quotient.mk zF) = 0
    rw [filtrationLayerMap_mkQ]
    have hdz : d.filtrationStage F H hd (p + 1) zF = 0 := by
      apply Subtype.ext
      exact hz
    rw [hdz]
    rfl
  have hrange : qz ∈ LinearMap.range (e.filtrationLayerMap P F he p) := by
    rw [hgr, LinearMap.mem_ker]
    exact hqz
  obtain ⟨qy, hqy⟩ := hrange
  obtain ⟨yP, rfl⟩ := Submodule.mkQ_surjective (Submodule.filtrationLower P p) qy
  refine ⟨yP.val, yP.property, ?_⟩
  have hzero : (Submodule.filtrationLower F p).mkQ
      (zF - e.filtrationStage P F he (p + 1) yP) = 0 := by
    rw [map_sub]
    change qz - e.filtrationLayerMap P F he p
      ((Submodule.filtrationLower P p).mkQ yP) = 0
    rw [hqy, sub_self]
  have hlower := (Submodule.Quotient.mk_eq_zero
    (Submodule.filtrationLower F p)).mp hzero
  exact hlower

/-- An exhaustive increasing filtration with zero initial middle stage
transfers exactness of its actual quotient sequence to the original maps.
The proof terminates at the finite stage containing each given cycle. -/
theorem range_eq_ker_of_exact_filtrationLayers
    (e : A →ₗ[R] B) (d : B →ₗ[R] C)
    (P : ℕ → Submodule R A) (F : ℕ → Submodule R B) (H : ℕ → Submodule R C)
    (he : ∀ p, ∀ x ∈ P p, e x ∈ F p)
    (hd : ∀ p, ∀ x ∈ F p, d x ∈ H p)
    (hde : d.comp e = 0)
    (hzero : F 0 = ⊥)
    (hexhaustive : ∀ z : B, ∃ p : ℕ, z ∈ F p)
    (hgr : ∀ p, LinearMap.range (e.filtrationLayerMap P F he p) =
      LinearMap.ker (d.filtrationLayerMap F H hd p)) :
    LinearMap.range e = LinearMap.ker d := by
  have hde_apply (y : A) : d (e y) = 0 := by
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
      LinearMap.congr_fun hde y
  have hfinite (p : ℕ) :
      ∀ z : B, z ∈ F p → d z = 0 → ∃ y : A, e y = z := by
    induction p with
    | zero =>
        intro z hz hdz
        rw [hzero, Submodule.mem_bot] at hz
        subst z
        exact ⟨0, e.map_zero⟩
    | succ p ih =>
        intro z hz hdz
        obtain ⟨y, _, hlower⟩ :=
          exists_boundary_mod_filtration e d P F H he hd p (hgr p) z hz hdz
        have hcycle : d (z - e y) = 0 := by
          rw [map_sub, hdz, hde_apply, sub_self]
        obtain ⟨y₀, hy₀⟩ := ih (z - e y) hlower hcycle
        refine ⟨y₀ + y, ?_⟩
        rw [map_add, hy₀, sub_add_cancel]
  apply le_antisymm
  · rintro z ⟨y, rfl⟩
    exact hde_apply y
  · intro z hz
    obtain ⟨p, hp⟩ := hexhaustive z
    exact hfinite p z hp hz

end LinearMap
