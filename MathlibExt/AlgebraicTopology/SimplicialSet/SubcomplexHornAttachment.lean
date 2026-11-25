/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-! # Attaching one simplex along a horn

If `σ : X _⦋m⦌` is a simplex whose classifying map is injective
on simplices and the preimage of a subcomplex `S` under
`yonedaEquiv.symm σ` is a horn `Λ[m, i]`, then `S ⊔ ofSimplex σ`
is the pushout of `Λ[m, i].ι` along the induced horn map
(`SSet.Subcomplex.isPushout_hornAttach`). Hence a map out of `S`
extends over the attached simplex as soon as the horn is filled
(`SSet.Subcomplex.exists_extension_sup_of_horn_filler`). This is
the single-cell case of the pushout argument of upstream
`RelativeCellComplex`/`Skeleton`.

This module is generic simplicial-set infrastructure: it depends
only on Mathlib horns, subcomplexes and pushouts in `Type`, with
no reference to any model structure.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped Simplicial

namespace SSet

/-- A simplex of `Δ[n]` whose range misses `i` lies in `∂Δ[n]`
(`SSet.mem_boundary_iff_notMem_range` restated pointwise). -/
lemma mem_boundary_of_forall_ne {n m : ℕ} (x : Δ[n] _⦋m⦌)
    (i : Fin (n + 1)) (h : ∀ t : Fin (m + 1), x t ≠ i) :
    x ∈ (∂Δ[n]).obj _ :=
  (mem_boundary_iff_notMem_range x).2 ⟨i, fun ⟨t, ht⟩ => h t ht⟩

section Attach

variable {X : SSet.{u}} {S : X.Subcomplex} {m : ℕ} {σ : X _⦋m⦌}
  {i : Fin (m + 1)}

/-- The horn map into `S` induced by a simplex whose `S`-preimage
is the horn `Λ[m, i]` (compare upstream `Cell.mapHorn`). -/
noncomputable def Subcomplex.hornLift (S : X.Subcomplex) (σ : X _⦋m⦌)
    (i : Fin (m + 1))
    (hpre : S.preimage (yonedaEquiv.symm σ) = Λ[m, i]) :
    (Λ[m, i] : SSet.{u}) ⟶ (S : SSet.{u}) :=
  Subcomplex.lift (Λ[m, i].ι ≫ yonedaEquiv.symm σ) (by
    simp [← Subcomplex.image_top, Subcomplex.image_le_iff,
      Subcomplex.preimage_comp, hpre])

@[reassoc (attr := simp)]
lemma Subcomplex.hornLift_ι (hpre : S.preimage (yonedaEquiv.symm σ) =
    Λ[m, i]) :
    Subcomplex.hornLift S σ i hpre ≫ S.ι =
      Λ[m, i].ι ≫ yonedaEquiv.symm σ :=
  rfl

/-- The classifying map of `σ`, lifted to `S ⊔ ofSimplex σ`. -/
noncomputable def Subcomplex.simplexLiftSup (S : X.Subcomplex)
    (σ : X _⦋m⦌) :
    Δ[m] ⟶ ((S ⊔ Subcomplex.ofSimplex σ : X.Subcomplex) : SSet.{u}) :=
  Subcomplex.lift (yonedaEquiv.symm σ) (by
    rw [Subcomplex.range_eq_ofSimplex, Equiv.apply_symm_apply]
    exact le_sup_right)

@[reassoc (attr := simp)]
lemma Subcomplex.simplexLiftSup_ι :
    Subcomplex.simplexLiftSup S σ ≫ (S ⊔ Subcomplex.ofSimplex σ).ι =
      yonedaEquiv.symm σ :=
  rfl

/-- The attaching square for one simplex along a horn commutes. -/
lemma Subcomplex.hornAttach_w (hpre :
    S.preimage (yonedaEquiv.symm σ) = Λ[m, i]) :
    Subcomplex.hornLift S σ i hpre ≫ Subcomplex.homOfLE le_sup_left =
      Λ[m, i].ι ≫ Subcomplex.simplexLiftSup S σ := by
  rw [← cancel_mono (S ⊔ Subcomplex.ofSimplex σ).ι, Category.assoc,
    Category.assoc, Subcomplex.homOfLE_ι, Subcomplex.hornLift_ι,
    Subcomplex.simplexLiftSup_ι]

end Attach

section AttachPushout

variable {X : SSet.{u}} {S : X.Subcomplex} {m : ℕ} {σ : X _⦋m⦌}
  {i : Fin (m + 1)}

/-- The attaching square of a simplex along a horn is a pullback:
simplices of `Δ[m]` landing in `S` are exactly the horn
simplices. The proof is the pointwise `Types.isPullback_iff`
argument of upstream `relativeCellComplexOfMono.isPullback`. -/
lemma Subcomplex.isPullback_hornAttach (hpre :
    S.preimage (yonedaEquiv.symm σ) = Λ[m, i]) :
    IsPullback (Subcomplex.hornLift S σ i hpre) Λ[m, i].ι
      (Subcomplex.homOfLE le_sup_left)
      (Subcomplex.simplexLiftSup S σ) where
  w := Subcomplex.hornAttach_w hpre
  isLimit' := ⟨evaluationJointlyReflectsLimits _ (fun ⟨⟨d⟩⟩ ↦ by
    refine (isLimitMapConePullbackConeEquiv _ _).2
      (IsPullback.isLimit ?_)
    dsimp
    rw [Types.isPullback_iff]
    refine ⟨NatTrans.congr_app (Subcomplex.hornAttach_w hpre) _,
      fun x₁ x₂ ⟨_, h⟩ ↦ Subtype.ext h,
      fun ⟨x, hx⟩ y h ↦ ?_⟩
    rw [Subtype.ext_iff] at h
    change x = (yonedaEquiv.symm σ).app _ y at h
    subst h
    have hy : y ∈ Λ[m, i].obj _ := by
      rw [← hpre, Subcomplex.preimage_obj, Set.mem_preimage]
      exact hx
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    apply Subtype.ext
    exact congr($(Subcomplex.hornLift_ι hpre).app _ ⟨y, hy⟩))⟩

/-- **The attaching square of a simplex along a horn is a
pushout**, when the classifying map of the simplex is injective
on simplices. The proof is `Types.isPushout_of_isPullback_of_mono'`
pointwise, as in upstream `relativeCellComplexOfMono.isPushout`:
pullback from `Subcomplex.isPullback_hornAttach`, joint
surjectivity from `S ⊔ ofSimplex σ`, and uniqueness from
injectivity. -/
lemma Subcomplex.isPushout_hornAttach (hpre :
      S.preimage (yonedaEquiv.symm σ) = Λ[m, i])
    (hinj : ∀ {d : ℕ} {s₁ s₂ : (Δ[m] : SSet.{u}) _⦋d⦌},
      (yonedaEquiv.symm σ).app _ s₁ =
        (yonedaEquiv.symm σ).app _ s₂ → s₁ = s₂) :
    IsPushout (Subcomplex.hornLift S σ i hpre) Λ[m, i].ι
      (Subcomplex.homOfLE le_sup_left)
      (Subcomplex.simplexLiftSup S σ) where
  w := Subcomplex.hornAttach_w hpre
  isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun ⟨⟨d⟩⟩ ↦ by
    refine (isColimitMapCoconePushoutCoconeEquiv _ _).2
      (IsPushout.isColimit ?_)
    refine Types.isPushout_of_isPullback_of_mono' ?_ ?_ ?_
    · exact (Subcomplex.isPullback_hornAttach hpre).map
        ((evaluation _ _).obj _)
    · rw [Set.eq_univ_iff_forall]
      rintro ⟨z, hz⟩
      rw [Subfunctor.max_obj] at hz
      rcases hz with hz | hz
      · exact Set.mem_union_left _ ⟨⟨z, hz⟩, Subtype.ext rfl⟩
      · have hEq : Subcomplex.ofSimplex σ =
            Subcomplex.range (yonedaEquiv.symm σ) := by
          rw [Subcomplex.range_eq_ofSimplex, Equiv.apply_symm_apply]
        rw [hEq, Subfunctor.range_obj] at hz
        obtain ⟨s, hs⟩ := hz
        exact Set.mem_union_right _ ⟨s, Subtype.ext hs⟩
    · dsimp
      intro x₁ x₂ _ _ h
      exact hinj (congrArg Subtype.val h))⟩

/-- Extending a map over one attached simplex: if the horn map
induced by `φ` is filled by `σC : Δ[m] ⟶ C`, then `φ` extends to
`S ⊔ ofSimplex σ` with prescribed value `σC` on the new simplex. -/
lemma Subcomplex.exists_extension_sup_of_horn_filler {C : SSet.{u}}
    (hpre : S.preimage (yonedaEquiv.symm σ) = Λ[m, i])
    (hinj : ∀ {d : ℕ} {s₁ s₂ : (Δ[m] : SSet.{u}) _⦋d⦌},
      (yonedaEquiv.symm σ).app _ s₁ =
        (yonedaEquiv.symm σ).app _ s₂ → s₁ = s₂)
    (φ : (S : SSet.{u}) ⟶ C) (σC : Δ[m] ⟶ C)
    (hσC : Subcomplex.hornLift S σ i hpre ≫ φ = Λ[m, i].ι ≫ σC) :
    ∃ φ' : ((S ⊔ Subcomplex.ofSimplex σ : X.Subcomplex) :
        SSet.{u}) ⟶ C,
      Subcomplex.homOfLE le_sup_left ≫ φ' = φ ∧
        Subcomplex.simplexLiftSup S σ ≫ φ' = σC :=
  ⟨(Subcomplex.isPushout_hornAttach hpre hinj).desc φ σC hσC,
    (Subcomplex.isPushout_hornAttach hpre hinj).inl_desc φ σC hσC,
    (Subcomplex.isPushout_hornAttach hpre hinj).inr_desc φ σC hσC⟩

end AttachPushout

end SSet
