/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.GrassmannianAdjoin

@[expose] public section

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry

universe u v w

/-- Consumer with the original `Type` and `Scheme.{0}` binders. -/
theorem exactSource
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ)
    (Gr : Scheme.{0}) (p : Gr ⟶ Spec (CommRingCat.of R))
    (pt : ∀ (A : Type) [CommRing A] [Algebra R A],
      Module.Grassmannian A (A ⊗[R] M) k ≃
        {g : Spec (CommRingCat.of A) ⟶ Gr //
          g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))})
    (hpt : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A]
      [Algebra R B] (φ : A →ₐ[R] B)
      (N : Module.Grassmannian A (A ⊗[R] M) k),
      (pt B (Module.Grassmannian.map φ N)).1 =
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt A N).1)
    (V : (Fin k → M) → Gr.Opens)
    (hVchart : ∀ (x : Fin k → M) (A : Type) [CommRing A] [Algebra R A]
      (N : Module.Grassmannian A (A ⊗[R] M) k),
      Set.range (pt A N).1.base ⊆ (V x : Set Gr) ↔
        Function.Bijective fun v : Fin k → A =>
          ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i))
    (ι : Type) (g : ι → M) (hg : Submodule.span R (Set.range g) = ⊤)
    (x : Fin k → M) (S : Type) [CommRing S] [Algebra R S]
    (N : Module.Grassmannian S (S ⊗[R] M) k)
    [IsOpenImmersion (pt S N).1] (hN : (pt S N).1.opensRange = V x) :
    Algebra.adjoin R {s : S | ∃ (a : ι) (c : Fin k → S) (i : Fin k),
        ∑ j, c j • N.toSubmodule.mkQ ((1 : S) ⊗ₜ[R] x j) =
            N.toSubmodule.mkQ ((1 : S) ⊗ₜ[R] g a) ∧
          s = c i} = ⊤ :=
  Module.Grassmannian.adjoin_eq_top_of_isOpenImmersion_of_opensRange_eq
    R M k Gr p pt hpt V hVchart ι g hg x S N hN

/-- The same consumer in higher universes. -/
example
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (k : ℕ) (Gr : Scheme.{u}) (p : Gr ⟶ Spec (CommRingCat.of R))
    (pt : ∀ (A : Type u) [CommRing A] [Algebra R A],
      Module.Grassmannian A (A ⊗[R] M) k ≃
        {g : Spec (CommRingCat.of A) ⟶ Gr //
          g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))})
    (hpt : ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra R A]
      [Algebra R B] (φ : A →ₐ[R] B)
      (N : Module.Grassmannian A (A ⊗[R] M) k),
      (pt B (Module.Grassmannian.map φ N)).1 =
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt A N).1)
    (V : (Fin k → M) → Gr.Opens)
    (hVchart : ∀ (x : Fin k → M) (A : Type u) [CommRing A] [Algebra R A]
      (N : Module.Grassmannian A (A ⊗[R] M) k),
      Set.range (pt A N).1.base ⊆ (V x : Set Gr) ↔
        Function.Bijective fun v : Fin k → A =>
          ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i))
    (ι : Type w) (g : ι → M) (hg : Submodule.span R (Set.range g) = ⊤)
    (x : Fin k → M) (S : Type u) [CommRing S] [Algebra R S]
    (N : Module.Grassmannian S (S ⊗[R] M) k)
    [IsOpenImmersion (pt S N).1] (hN : (pt S N).1.opensRange = V x) :
    Algebra.adjoin R {s : S | ∃ (a : ι) (c : Fin k → S) (i : Fin k),
        ∑ j, c j • N.toSubmodule.mkQ ((1 : S) ⊗ₜ[R] x j) =
            N.toSubmodule.mkQ ((1 : S) ⊗ₜ[R] g a) ∧
          s = c i} = ⊤ :=
  Module.Grassmannian.adjoin_eq_top_of_isOpenImmersion_of_opensRange_eq
    R M k Gr p pt hpt V hVchart ι g hg x S N hN

/-- The spanning hypothesis is not automatic: the empty family does not
span `ℚ` as a module over itself. -/
example : Submodule.span ℚ (Set.range (fun a : Fin 0 => (a.elim0 : ℚ))) ≠ ⊤ := by
  simp
