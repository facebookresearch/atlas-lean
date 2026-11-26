/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer reproduces the theorem type from
`Theorems/Thm_Module_Grassmannian_adjoin_eq_top_of_isOpenImmersion_of_opensRange_eq.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

public import MathlibExt.AlgebraicGeometry.GrassmannianAdjoin

@[expose] public section

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry

universe u v w

/-- Consumer with the original `Type` and `Scheme.{0}` binders. -/
private theorem exactSource
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

/-! ### A concrete instance in rank zero

For `k = 0` the Grassmannian functor is represented by `Spec R` itself: over every `A`
the only point is `⊤`, because a finite projective quotient of rank `0` vanishes. The chart
at the empty family is then all of `Spec R`, and the identity point of `Spec R` meets every
hypothesis of `Module.Grassmannian.adjoin_eq_top_of_isOpenImmersion_of_opensRange_eq`. -/

section RankZero

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/-- Every point of `G(0, A ⊗[R] M; A)` is the whole module. -/
private theorem toSubmodule_eq_top_of_rank_zero {A : Type u} [CommRing A] [Algebra R A]
    (N : Module.Grassmannian A (A ⊗[R] M) 0) : N.toSubmodule = ⊤ := by
  have h : Module.rankAtStalk (R := A) ((A ⊗[R] M) ⧸ N.toSubmodule) = 0 := by
    ext p
    exact N.rankAtStalk_eq p
  exact Submodule.Quotient.subsingleton_iff.mp
    (Module.rankAtStalk_eq_zero_iff_subsingleton.mp h)

/-- The point `⊤` of `G(0, A ⊗[R] M; A)`. -/
private def topPoint (A : Type u) [CommRing A] [Algebra R A] :
    Module.Grassmannian A (A ⊗[R] M) 0 :=
  have : Subsingleton ((A ⊗[R] M) ⧸ (⊤ : Submodule A (A ⊗[R] M))) :=
    Submodule.Quotient.subsingleton_iff.mpr rfl
  { toSubmodule := ⊤
    finite_quotient := inferInstance
    projective_quotient := inferInstance
    rankAtStalk_eq := fun p => by simp }

private instance (A : Type u) [CommRing A] [Algebra R A] :
    Unique (Module.Grassmannian A (A ⊗[R] M) 0) where
  default := topPoint R M A
  uniq N := Module.Grassmannian.ext (toSubmodule_eq_top_of_rank_zero R M N)

/-- `Spec R` with the identity represents `A ↦ G(0, A ⊗[R] M; A)`: both sides are points. -/
private noncomputable def pt0 (A : Type u) [CommRing A] [Algebra R A] :
    Module.Grassmannian A (A ⊗[R] M) 0 ≃
      {g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) //
        g ≫ 𝟙 _ = Spec.map (CommRingCat.ofHom (algebraMap R A))} where
  toFun _ := ⟨Spec.map (CommRingCat.ofHom (algebraMap R A)), Category.comp_id _⟩
  invFun _ := default
  left_inv _ := Subsingleton.elim _ _
  right_inv g := Subtype.ext ((Category.comp_id g.1).symm.trans g.2).symm

private theorem pt0_natural (A B : Type u) [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (φ : A →ₐ[R] B) (N : Module.Grassmannian A (A ⊗[R] M) 0) :
    (pt0 R M B (Module.Grassmannian.map φ N)).1 =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt0 R M A N).1 := by
  change Spec.map (CommRingCat.ofHom (algebraMap R B)) =
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))
  rw [← Spec.map_comp]
  congr 1
  ext a
  simp

/-- The chart at the empty family is all of `Spec R`. -/
private theorem pt0_chart (x : Fin 0 → M) (A : Type u) [CommRing A] [Algebra R A]
    (N : Module.Grassmannian A (A ⊗[R] M) 0) :
    Set.range (pt0 R M A N).1.base ⊆ ((⊤ : (Spec (CommRingCat.of R)).Opens) : Set _) ↔
      Function.Bijective fun v : Fin 0 → A =>
        ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i) := by
  have : Subsingleton ((A ⊗[R] M) ⧸ N.toSubmodule) :=
    Submodule.Quotient.subsingleton_iff.mpr (toSubmodule_eq_top_of_rank_zero R M N)
  exact iff_of_true (fun _ _ => trivial)
    ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

private theorem pt0_self (N : Module.Grassmannian R (R ⊗[R] M) 0) :
    (pt0 R M R N).1 = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (algebraMap R R)) = 𝟙 _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

/-- Every hypothesis of the theorem holds at `k = 0` for `Gr = Spec R`, the chart `⊤` and the
identity point; here the coordinate set is empty, so the conclusion says `R` is generated by
nothing over itself. -/
example :
    Algebra.adjoin R {s : R | ∃ (a : M) (c : Fin 0 → R) (i : Fin 0),
        ∑ j, c j • (default : Module.Grassmannian R (R ⊗[R] M) 0).toSubmodule.mkQ
            ((1 : R) ⊗ₜ[R] (![] : Fin 0 → M) j) =
          (default : Module.Grassmannian R (R ⊗[R] M) 0).toSubmodule.mkQ
            ((1 : R) ⊗ₜ[R] a) ∧
        s = c i} = ⊤ := by
  have : IsIso (pt0 R M R default).1 := by
    rw [pt0_self R M]
    infer_instance
  exact Module.Grassmannian.adjoin_eq_top_of_isOpenImmersion_of_opensRange_eq R M 0
    (Spec (CommRingCat.of R)) (𝟙 _) (pt0 R M) (pt0_natural R M) (fun _ => ⊤) (pt0_chart R M)
    M id (by rw [Set.range_id, Submodule.span_univ]) ![] R default
    (Scheme.Hom.opensRange_of_isIso _)

end RankZero
