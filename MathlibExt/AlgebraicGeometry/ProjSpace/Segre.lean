/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_ChowDatumProj_nonempty_of.lean` and
`P2M/Sol/S_AlgebraicGeometry_ChowDatumProj_nonempty_of.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the definitions and proofs are reused here with that machinery
removed and the names restated in Mathlib style.

The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import MathlibExt.AlgebraicGeometry.ProjSpace.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The Segre embedding

For a commutative ring `R`, the fibre product over `Spec R` of projective
`n`-space and projective `p`-space admits a closed immersion over `Spec R`
into projective `((n + 1) * (p + 1) - 1)`-space, given on product charts by
`Z (k, l) ↦ (X k / X i) ⊗ (Y l / Y j)`. Iterating it, every finite fibre
product `prodOver R e` of projective spaces embeds as a closed subscheme of a
single projective space over `Spec R` (`ProjSpace.Segre.segreAux`).
-/

-- Several chart computations unify through cover index types and
-- `HomogeneousLocalization` instances that are only defeq at default
-- transparency.
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
open HomogeneousLocalization TensorProduct

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjSpace
namespace Segre

section ChartHom

variable (R : Type u) [CommRing R] (n p : ℕ)

/-- The dimension `(n + 1) * (p + 1) - 1` of the target of the Segre
embedding of a product of projective `n`- and `p`-space. -/
abbrev bigN : ℕ := (n + 1) * (p + 1) - 1

theorem bigN_succ :
    (n + 1) * (p + 1) = bigN n p + 1 := by
  have h : 0 < (n + 1) * (p + 1) := Nat.mul_pos (Nat.succ_pos n) (Nat.succ_pos p)
  unfold bigN; omega

/-- Indexing of the Segre coordinates `Z (k, l)` by `Fin (bigN n p + 1)`. -/
def idx : Fin (n + 1) × Fin (p + 1) ≃ Fin (bigN n p + 1) :=
  finProdFinEquiv.trans (finCongr (bigN_succ n p))

variable (i : Fin (n + 1)) (j : Fin (p + 1))

local notation "N" => bigN n p
local notation "𝒜ˣ" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "𝒜ʸ" => MvPolynomial.homogeneousSubmodule (Fin (p + 1)) R
local notation "𝒜ᶻ" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

/-- The coordinate ring `D₊(X i) ⊗[R] D₊(Y j)` of a product chart. -/
abbrev Tij : Type u :=
  (Away 𝒜ˣ (MvPolynomial.X i)) ⊗[R] (Away 𝒜ʸ (MvPolynomial.X j))

local notation "Aˣ" => Away 𝒜ˣ (MvPolynomial.X i)
local notation "Aʸ" => Away 𝒜ʸ (MvPolynomial.X j)

/-- The `R`-algebra map sending `Z (k, l)` to `(X k / X i) ⊗ (Y l / Y j)`. -/
def preSegre : MvPolynomial (Fin (N + 1)) R →ₐ[R] (Aˣ ⊗[R] Aʸ) :=
  MvPolynomial.aeval
    (fun α => ((ProjSpace.ratio R n i ((idx n p).symm α).1)
      ⊗ₜ[R] (ProjSpace.ratio R p j ((idx n p).symm α).2) : Aˣ ⊗[R] Aʸ))

theorem preSegre_apply (k : Fin (n + 1)) (l : Fin (p + 1)) :
    preSegre R n p i j (MvPolynomial.X (idx n p (k, l)))
      = ((ProjSpace.ratio R n i k) ⊗ₜ[R] (ProjSpace.ratio R p j l) :
          Aˣ ⊗[R] Aʸ) := by
  unfold preSegre
  rw [MvPolynomial.aeval_X, Equiv.symm_apply_apply]

theorem preSegre_unit :
    (preSegre R n p i j).toRingHom
        (MvPolynomial.X (idx n p (i, j))) = 1 := by
  change preSegre R n p i j (MvPolynomial.X (idx n p (i, j))) = 1
  rw [preSegre_apply, ProjSpace.ratio_self, ProjSpace.ratio_self,
    Algebra.TensorProduct.one_def]

theorem preSegre_mulone :
    (preSegre R n p i j).toRingHom
        (X (idx n p (i, j))) * 1 = 1 := by
  rw [preSegre_unit, mul_one]

/-- `preSegre` extended to the localization away from `Z (i, j)`. -/
def segreLift :
    Localization.Away (X (idx n p (i, j)) :
      MvPolynomial (Fin (N + 1)) R) →+* Tij R n p i j :=
  Localization.awayLift (preSegre R n p i j).toRingHom
    (MvPolynomial.X (idx n p (i, j)))
    ⟨⟨(preSegre R n p i j).toRingHom (X (idx n p (i, j))),
      1, preSegre_mulone R n p i j,
      (one_mul _).trans (preSegre_unit R n p i j)⟩, rfl⟩

/-- The Segre map on coordinate rings of the chart `D₊(Z (i, j))`. -/
def segreChart :
    Away 𝒜ᶻ (MvPolynomial.X (idx n p (i, j)))
      →+* Tij R n p i j :=
  (segreLift R n p i j).comp
    (algebraMap (Away 𝒜ᶻ (MvPolynomial.X (idx n p (i, j))))
      (Localization.Away (MvPolynomial.X (idx n p (i, j)))))

theorem segreChart_ratio (k : Fin (n + 1)) (l : Fin (p + 1)) :
    segreChart R n p i j
        (ProjSpace.ratio R N (idx n p (i, j))
          (idx n p (k, l)))
      = ((ProjSpace.ratio R n i k) ⊗ₜ[R] (ProjSpace.ratio R p j l) :
          Tij R n p i j) := by
  unfold segreChart segreLift Localization.awayLift
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    ProjSpace.ratio, Away.val_mk, Localization.mk_eq_mk', IsLocalization.Away.lift,
    IsLocalization.lift_mk'_spec, map_pow, pow_one, preSegre_unit, one_mul]
  exact preSegre_apply R n p i j k l

theorem segreChart_algebraMap (r : R) :
    segreChart R n p i j
        (algebraMap R (Away 𝒜ᶻ (X (idx n p (i, j)))) r)
      = ((1 : Aˣ) ⊗ₜ[R] algebraMap R Aʸ r : Aˣ ⊗[R] Aʸ) := by
  unfold segreChart segreLift
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    ProjSpace.val_algebraMap]
  erw [IsLocalization.lift_eq]
  have := (preSegre R n p i j).commutes r
  rw [Algebra.TensorProduct.algebraMap_apply'] at this
  exact this

theorem segreChart_surjective :
    Function.Surjective (segreChart R n p i j) := by
  intro z
  suffices h : z ∈ (segreChart R n p i j).range from h
  have hswap : ∀ r, ((1:Aˣ) ⊗ₜ[R] algebraMap R Aʸ r : Aˣ ⊗[R] Aʸ)
      = (algebraMap R Aˣ r) ⊗ₜ[R] (1:Aʸ) := fun r => by
    rw [Algebra.algebraMap_eq_smul_one (A := Aʸ), Algebra.algebraMap_eq_smul_one (A := Aˣ)]
    exact (TensorProduct.smul_tmul r (1:Aˣ) (1:Aʸ)).symm
  have hR : ∀ r, ((algebraMap R Aˣ r) ⊗ₜ[R] (1 : Aʸ) : Aˣ ⊗[R] Aʸ)
      ∈ (segreChart R n p i j).range :=
    fun r => ⟨algebraMap R _ r,
      (segreChart_algebraMap R n p i j r).trans (hswap r)⟩
  have hx : ∀ k, (ProjSpace.ratio R n i k ⊗ₜ[R] (1 : Aʸ) : Aˣ ⊗[R] Aʸ)
      ∈ (segreChart R n p i j).range := fun k => by
    rw [show (1 : Aʸ) = ProjSpace.ratio R p j j from (ProjSpace.ratio_self R p j).symm]
    exact ⟨_, segreChart_ratio R n p i j k j⟩
  have hy : ∀ l, ((1 : Aˣ) ⊗ₜ[R] ProjSpace.ratio R p j l : Aˣ ⊗[R] Aʸ)
      ∈ (segreChart R n p i j).range := fun l => by
    rw [show (1 : Aˣ) = ProjSpace.ratio R n i i from (ProjSpace.ratio_self R n i).symm]
    exact ⟨_, segreChart_ratio R n p i j i l⟩
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => exact Subring.add_mem _ ha hb
  | tmul a b =>
    rw [show (a ⊗ₜ[R] b : Aˣ ⊗[R] Aʸ) = (a ⊗ₜ[R] (1:Aʸ)) * ((1:Aˣ) ⊗ₜ[R] b) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
    refine Subring.mul_mem _ ?_ ?_
    · have ha : a ∈ Algebra.adjoin R (Set.range (ProjSpace.ratio R n i)) := by
        rw [ProjSpace.adjoin_range_ratio]; exact Algebra.mem_top
      refine Algebra.adjoin_induction
        (fun c ⟨k, hk⟩ => hk ▸ hx k)
        (fun r => ?_)
        (fun a b _ _ ha hb => by rw [TensorProduct.add_tmul]; exact Subring.add_mem _ ha hb)
        (fun a b _ _ ha hb => by
          rw [show ((a * b) ⊗ₜ[R] (1:Aʸ) : Aˣ ⊗[R] Aʸ) = (a ⊗ₜ 1) * (b ⊗ₜ 1) by
            rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]]
          exact Subring.mul_mem _ ha hb)
        ha
      exact hR r
    · have hb : b ∈ Algebra.adjoin R (Set.range (ProjSpace.ratio R p j)) := by
        rw [ProjSpace.adjoin_range_ratio]; exact Algebra.mem_top
      refine Algebra.adjoin_induction
        (fun c ⟨l, hl⟩ => hl ▸ hy l)
        (fun r => ?_)
        (fun a b _ _ ha hb => by rw [TensorProduct.tmul_add]; exact Subring.add_mem _ ha hb)
        (fun a b _ _ ha hb => by
          rw [show ((1:Aˣ) ⊗ₜ[R] (a * b) : Aˣ ⊗[R] Aʸ) = (1 ⊗ₜ a) * (1 ⊗ₜ b) by
            rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]]
          exact Subring.mul_mem _ ha hb)
        hb
      rw [hswap r]; exact hR r

end ChartHom

section ProductCover

variable (R : Type u) [CommRing R] (n p : ℕ)

local notation "N" => bigN n p
local notation "𝒜ˣ" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "𝒜ʸ" => MvPolynomial.homogeneousSubmodule (Fin (p + 1)) R
local notation "𝒜ᶻ" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

/-- The open cover of a product of two projective spaces by products of
standard charts. -/
abbrev prodCover :
    (pullback (ProjSpace.π R n) (ProjSpace.π R p)).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight
    (ProjSpace.affineOpenCover R n).openCover (ProjSpace.affineOpenCover R p).openCover _ _

/-- A product chart is `Spec` of the tensor product of the chart rings. -/
def chartIso (i : Fin (n + 1)) (j : Fin (p + 1)) :
    (prodCover R n p).X (i, j)
      ≅ Spec (.of <| (Away 𝒜ˣ (X i)) ⊗[R] (Away 𝒜ʸ (X j))) :=
  pullback.congrHom (ProjSpace.awayι_comp_π R n i) (ProjSpace.awayι_comp_π R p j)
    ≪≫ pullbackSpecIso R (Away 𝒜ˣ (X i)) (Away 𝒜ʸ (X j))

/-- The Segre map on one product chart, landing in projective space. -/
def chartMap (i : Fin (n + 1)) (j : Fin (p + 1)) :
    (prodCover R n p).X (i, j) ⟶ Proj 𝒜ᶻ :=
  (chartIso R n p i j).hom
    ≫ Spec.map (CommRingCat.ofHom (segreChart R n p i j))
    ≫ Proj.awayι 𝒜ᶻ (MvPolynomial.X (idx n p (i, j)))
        (ProjSpace.X_mem_one R N (idx n p (i, j))) one_pos

theorem chartMap_over (ij : Fin (n + 1) × Fin (p + 1)) :
    chartMap R n p ij.1 ij.2 ≫ ProjSpace.π R N
      = (prodCover R n p).f ij
          ≫ pullback.fst _ _ ≫ ProjSpace.π R n := by
  obtain ⟨i, j⟩ := ij
  change Fin (n + 1) at i; change Fin (p + 1) at j
  change chartMap R n p i j ≫ ProjSpace.π R N
    = (prodCover R n p).f (i, j) ≫ pullback.fst _ _ ≫ ProjSpace.π R n
  rw [chartMap, Category.assoc, Category.assoc, ProjSpace.awayι_comp_π,
    chartIso, Iso.trans_hom, Category.assoc]
  conv_rhs =>
    dsimp only [prodCover, Scheme.Pullback.openCoverOfLeftRight_f]
    rw [← Category.assoc]
    erw [pullback.lift_fst]
    erw [Category.assoc]
    enter [2]
    rw [show (ProjSpace.affineOpenCover R n).openCover.f i ≫ ProjSpace.π R n
        = Spec.map (CommRingCat.ofHom (algebraMap R (Away 𝒜ˣ (X i))))
      from ProjSpace.awayι_comp_π R n i]
  have hcong : (pullback.fst _ _
          : pullback ((ProjSpace.affineOpenCover R n).openCover.f i ≫ ProjSpace.π R n)
              ((ProjSpace.affineOpenCover R p).openCover.f j ≫ ProjSpace.π R p) ⟶ _)
        ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Away 𝒜ˣ (X i))))
      = (pullback.congrHom (ProjSpace.awayι_comp_π R n i)
          (ProjSpace.awayι_comp_π R p j)).hom
        ≫ pullback.fst _ _
        ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Away 𝒜ˣ (X i)))) := by
    rw [pullback.congrHom_hom, ← Category.assoc, pullback.lift_fst, Category.comp_id]; rfl
  erw [hcong]
  suffices h : (pullbackSpecIso R (Away 𝒜ˣ (X i)) (Away 𝒜ʸ (X j))).hom
        ≫ Spec.map (CommRingCat.ofHom (segreChart R n p i j))
        ≫ Spec.map (CommRingCat.ofHom
            (algebraMap R (Away 𝒜ᶻ (X (idx n p (i, j))))))
      = pullback.fst _ _
        ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Away 𝒜ˣ (X i)))) by rw [h]
  erw [← pullbackSpecIso_hom_fst_assoc R (Away 𝒜ˣ (X i)) (Away 𝒜ʸ (X j))]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 2
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  change segreChart R n p i j (algebraMap R _ r)
    = Algebra.TensorProduct.includeLeftRingHom (algebraMap R (Away 𝒜ˣ (X i)) r)
  rw [segreChart_algebraMap, Algebra.TensorProduct.includeLeftRingHom_apply,
    Algebra.algebraMap_eq_smul_one (R := R) (A := Away 𝒜ʸ (X j)),
    Algebra.algebraMap_eq_smul_one (R := R) (A := Away 𝒜ˣ (X i))]
  exact (TensorProduct.smul_tmul r (1 : Away 𝒜ˣ (X i)) (1 : Away 𝒜ʸ (X j))).symm

@[reassoc]
theorem prodCover_fst (ij : Fin (n + 1) × Fin (p + 1)) :
    (prodCover R n p).f ij ≫ pullback.fst _ _
      = (pullback.fst _ _ : (prodCover R n p).X ij ⟶ _)
        ≫ Proj.awayι 𝒜ˣ (X ij.1) (ProjSpace.X_mem_one R n ij.1) one_pos := by
  dsimp only [prodCover, Scheme.Pullback.openCoverOfLeftRight_f]
  erw [pullback.lift_fst]; rfl

@[reassoc]
theorem prodCover_snd (ij : Fin (n + 1) × Fin (p + 1)) :
    (prodCover R n p).f ij ≫ pullback.snd _ _
      = (pullback.snd _ _ : (prodCover R n p).X ij ⟶ _)
        ≫ Proj.awayι 𝒜ʸ (X ij.2) (ProjSpace.X_mem_one R p ij.2) one_pos := by
  dsimp only [prodCover, Scheme.Pullback.openCoverOfLeftRight_f]
  erw [pullback.lift_snd]; rfl

@[reassoc]
theorem chartIso_incL (i : Fin (n + 1)) (j : Fin (p + 1)) :
    (chartIso R n p i j).hom
        ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
            (A := Away 𝒜ˣ (X i)) (B := Away 𝒜ʸ (X j))))
      = pullback.fst _ _ := by
  rw [chartIso, Iso.trans_hom, Category.assoc]
  erw [pullbackSpecIso_hom_fst R (Away 𝒜ˣ (X i)) (Away 𝒜ʸ (X j))]
  rw [pullback.congrHom_hom]
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc]
theorem chartIso_incR (i : Fin (n + 1)) (j : Fin (p + 1)) :
    (chartIso R n p i j).hom
        ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
            (R := R) (A := Away 𝒜ˣ (X i)) (B := Away 𝒜ʸ (X j))).toRingHom)
      = pullback.snd _ _ := by
  rw [chartIso, Iso.trans_hom, Category.assoc]
  erw [pullbackSpecIso_hom_snd R (Away 𝒜ˣ (X i)) (Away 𝒜ʸ (X j))]
  rw [pullback.congrHom_hom]
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem isLocElem_ratio (i k : Fin (n + 1)) :
    HomogeneousLocalization.Away.isLocalizationElem
        (ProjSpace.X_mem_one R n i) (ProjSpace.X_mem_one R n k)
      = ProjSpace.ratio R n i k := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.isLocalizationElem,
    HomogeneousLocalization.Away.val_mk, ProjSpace.ratio, pow_one]

theorem range_SpecMap_awayMap (i k : Fin (n + 1)) :
    Set.range (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ˣ
        (ProjSpace.X_mem_one R n k)
        (rfl : (X i * X k : MvPolynomial (Fin (n+1)) R) = X i * X k)))).base
      = (PrimeSpectrum.basicOpen (ProjSpace.ratio R n i k)
          : Set (PrimeSpectrum (Away 𝒜ˣ (X i)))) := by
  let := (HomogeneousLocalization.awayMap 𝒜ˣ (ProjSpace.X_mem_one R n k)
    (rfl : (X i * X k : MvPolynomial (Fin (n+1)) R) = X i * X k)).toAlgebra
  let := HomogeneousLocalization.Away.isLocalization_mul
    (ProjSpace.X_mem_one R n i) (ProjSpace.X_mem_one R n k) rfl one_ne_zero
  rw [← isLocElem_ratio R n i k]
  exact PrimeSpectrum.localization_away_comap_range _ _

theorem opensRange_prodCover_f (α : Fin (n + 1) × Fin (p + 1)) :
    ((prodCover R n p).f α).opensRange
      = pullback.fst (ProjSpace.π R n) (ProjSpace.π R p)
          ⁻¹ᵁ (Proj.awayι 𝒜ˣ (X α.1) (ProjSpace.X_mem_one R n α.1) one_pos).opensRange
        ⊓ pullback.snd (ProjSpace.π R n) (ProjSpace.π R p)
          ⁻¹ᵁ (Proj.awayι 𝒜ʸ (X α.2) (ProjSpace.X_mem_one R p α.2) one_pos).opensRange := by
  have key : Set.range ((prodCover R n p).f α).base
      = (pullback.fst (ProjSpace.π R n) (ProjSpace.π R p)).base ⁻¹' Set.range
          ((ProjSpace.affineOpenCover R n).openCover.f α.1).base
        ∩ (pullback.snd (ProjSpace.π R n) (ProjSpace.π R p)).base ⁻¹' Set.range
          ((ProjSpace.affineOpenCover R p).openCover.f α.2).base := by
    dsimp only [prodCover, Scheme.Pullback.openCoverOfLeftRight_f]
    exact Scheme.Pullback.range_map _ _ (ProjSpace.π R n) (ProjSpace.π R p)
      ((ProjSpace.affineOpenCover R n).openCover.f α.1)
      ((ProjSpace.affineOpenCover R p).openCover.f α.2) (𝟙 _)
      (Category.comp_id _) (Category.comp_id _)
  exact TopologicalSpace.Opens.ext key

theorem awayMap_ratio_transition (i k a : Fin (n + 1)) :
    (HomogeneousLocalization.awayMap 𝒜ˣ (ProjSpace.X_mem_one R n i)
        (mul_comm (X i) (X k) : (X i * X k : MvPolynomial (Fin (n+1)) R) = X k * X i))
      (ProjSpace.ratio R n k a)
    * (HomogeneousLocalization.awayMap 𝒜ˣ (ProjSpace.X_mem_one R n k)
        (rfl : (X i * X k : MvPolynomial (Fin (n+1)) R) = X i * X k))
      (ProjSpace.ratio R n i k)
    = (HomogeneousLocalization.awayMap 𝒜ˣ (ProjSpace.X_mem_one R n k)
        (rfl : (X i * X k : MvPolynomial (Fin (n+1)) R) = X i * X k))
      (ProjSpace.ratio R n i a) := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, ProjSpace.ratio,
    HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk,
    pow_one, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by push_cast; ring⟩

theorem overlap_fst_condition (ij kl : Fin (n + 1) × Fin (p + 1)) :
    (pullback.fst ((prodCover R n p).f ij)
          ((prodCover R n p).f kl)
        ≫ (chartIso R n p ij.1 ij.2).hom
        ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
      ≫ Proj.awayι 𝒜ˣ (X ij.1) (ProjSpace.X_mem_one R n ij.1) one_pos
    = (pullback.snd _ _
        ≫ (chartIso R n p kl.1 kl.2).hom
        ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
      ≫ Proj.awayι 𝒜ˣ (X kl.1) (ProjSpace.X_mem_one R n kl.1) one_pos := by
  simp only [Category.assoc]
  erw [chartIso_incL_assoc R n p ij.1 ij.2,
    chartIso_incL_assoc R n p kl.1 kl.2]
  erw [← prodCover_fst R n p ij, ← prodCover_fst R n p kl]
  rw [← Category.assoc, pullback.condition, Category.assoc]

theorem overlap_snd_condition (ij kl : Fin (n + 1) × Fin (p + 1)) :
    (pullback.fst ((prodCover R n p).f ij)
          ((prodCover R n p).f kl)
        ≫ (chartIso R n p ij.1 ij.2).hom
        ≫ Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight (R := R)).toRingHom))
      ≫ Proj.awayι 𝒜ʸ (X ij.2) (ProjSpace.X_mem_one R p ij.2) one_pos
    = (pullback.snd _ _
        ≫ (chartIso R n p kl.1 kl.2).hom
        ≫ Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight (R := R)).toRingHom))
      ≫ Proj.awayι 𝒜ʸ (X kl.2) (ProjSpace.X_mem_one R p kl.2) one_pos := by
  simp only [Category.assoc]
  erw [chartIso_incR_assoc R n p ij.1 ij.2,
    chartIso_incR_assoc R n p kl.1 kl.2]
  erw [← prodCover_snd R n p ij, ← prodCover_snd R n p kl]
  rw [← Category.assoc, pullback.condition, Category.assoc]

set_option maxHeartbeats 800000 in
-- Gluing the chart maps elaborates large pullback and localization terms.
theorem chartMap_compat (ij kl : Fin (n + 1) × Fin (p + 1)) :
    pullback.fst ((prodCover R n p).f ij)
        ((prodCover R n p).f kl)
      ≫ chartMap R n p ij.1 ij.2
    = pullback.snd _ _ ≫ chartMap R n p kl.1 kl.2 := by
  obtain ⟨i, j⟩ := ij; obtain ⟨k, l⟩ := kl
  change Fin (n + 1) at i; change Fin (n + 1) at k
  change Fin (p + 1) at j; change Fin (p + 1) at l
  simp only [chartMap, ← Category.assoc]
  set fstW := pullback.fst ((prodCover R n p).f (i, j))
    ((prodCover R n p).f (k, l)) with hfstW
  set sndW := pullback.snd ((prodCover R n p).f (i, j))
    ((prodCover R n p).f (k, l)) with hsndW
  set φ_ij := (fstW ≫ (chartIso R n p i j).hom)
    ≫ Spec.map (CommRingCat.ofHom (segreChart R n p i j)) with hφij
  set φ_kl := (sndW ≫ (chartIso R n p k l).hom)
    ≫ Spec.map (CommRingCat.ofHom (segreChart R n p k l)) with hφkl
  change φ_ij ≫ Proj.awayι 𝒜ᶻ (X (idx n p (i, j)))
      (ProjSpace.X_mem_one R N _) one_pos
    = φ_kl ≫ Proj.awayι 𝒜ᶻ (X (idx n p (k, l)))
      (ProjSpace.X_mem_one R N _) one_pos
  let ηx := pullback.lift
    (fstW ≫ (chartIso R n p i j).hom
      ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
    (sndW ≫ (chartIso R n p k l).hom
      ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
    (overlap_fst_condition R n p (i, j) (k, l))
  let ηx' := ηx ≫ (Proj.pullbackAwayιIso 𝒜ˣ (ProjSpace.X_mem_one R n i) one_pos
    (ProjSpace.X_mem_one R n k) one_pos
    (rfl : (X i * X k : MvPolynomial (Fin (n+1)) R) = X i * X k)).hom
  have hηx_fst : ηx' ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ˣ
      (ProjSpace.X_mem_one R n k) rfl))
      = fstW ≫ (chartIso R n p i j).hom
        ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := by
    rw [Category.assoc, Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left, pullback.lift_fst]
  have hηx_snd : ηx' ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ˣ
      (ProjSpace.X_mem_one R n i) (mul_comm _ _)))
      = sndW ≫ (chartIso R n p k l).hom
        ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := by
    rw [show (mul_comm (X i) (X k) : (X i * X k : MvPolynomial (Fin (n+1)) R) = X k * X i)
      = (rfl : (_ : MvPolynomial (Fin (n+1)) R) = X i * X k).trans (mul_comm _ _) from rfl]
    rw [Category.assoc, Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right, pullback.lift_snd]
  let ηy := pullback.lift
    (fstW ≫ (chartIso R n p i j).hom
      ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R)).toRingHom))
    (sndW ≫ (chartIso R n p k l).hom
      ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R)).toRingHom))
    (overlap_snd_condition R n p (i, j) (k, l))
  let ηy' := ηy ≫ (Proj.pullbackAwayιIso 𝒜ʸ (ProjSpace.X_mem_one R p j) one_pos
    (ProjSpace.X_mem_one R p l) one_pos
    (rfl : (X j * X l : MvPolynomial (Fin (p+1)) R) = X j * X l)).hom
  have hηy_fst : ηy' ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ʸ
      (ProjSpace.X_mem_one R p l) rfl))
      = fstW ≫ (chartIso R n p i j).hom
        ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := R)).toRingHom) := by
    rw [Category.assoc, Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left, pullback.lift_fst]
  have hηy_snd : ηy' ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ʸ
      (ProjSpace.X_mem_one R p j) (mul_comm _ _)))
      = sndW ≫ (chartIso R n p k l).hom
        ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := R)).toRingHom) := by
    rw [show (mul_comm (X j) (X l) : (X j * X l : MvPolynomial (Fin (p+1)) R) = X l * X j)
      = (rfl : (_ : MvPolynomial (Fin (p+1)) R) = X j * X l).trans (mul_comm _ _) from rfl]
    rw [Category.assoc, Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right, pullback.lift_snd]
  have hoi : IsOpenImmersion (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ᶻ
      (ProjSpace.X_mem_one R N (idx n p (k, l)))
      (rfl : (X (idx n p (i, j)) * X (idx n p (k, l))
        : MvPolynomial (Fin (N+1)) R) = _)))) := by
    rw [← Proj.pullbackAwayιIso_inv_fst 𝒜ᶻ (ProjSpace.X_mem_one R N _) one_pos
      (ProjSpace.X_mem_one R N _) one_pos rfl]
    infer_instance
  have hrange : Set.range (φ_ij).base ⊆ Set.range
      (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ᶻ
        (ProjSpace.X_mem_one R N (idx n p (k, l)))
        (rfl : (X (idx n p (i, j)) * X (idx n p (k, l))
          : MvPolynomial (Fin (N+1)) R) = _)))).base := by
    rw [range_SpecMap_awayMap R N
      (idx n p (i, j)) (idx n p (k, l))]
    rintro _ ⟨w, rfl⟩
    change ProjSpace.ratio R N _ _ ∉ (φ_ij.base w).asIdeal
    intro habs
    have hψ : segreChart R n p i j (ProjSpace.ratio R N
        (idx n p (i, j)) (idx n p (k, l)))
        ∈ ((fstW ≫ (chartIso R n p i j).hom).base w).asIdeal := habs
    rw [segreChart_ratio,
      show (ProjSpace.ratio R n i k ⊗ₜ[R] ProjSpace.ratio R p j l
        : Tij R n p i j)
      = (ProjSpace.ratio R n i k ⊗ₜ[R] 1) * (1 ⊗ₜ[R] ProjSpace.ratio R p j l) from by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]] at hψ
    rcases ((fstW ≫ (chartIso R n p i j).hom).base w).isPrime.mem_or_mem hψ
      with hψ' | hψ'
    · refine absurd ?_
        (show ProjSpace.ratio R n i k ∉ ((fstW ≫ (chartIso R n p i j).hom
          ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)).base w).asIdeal
          from by
            rw [← hηx_fst, Scheme.Hom.comp_apply]
            exact (range_SpecMap_awayMap R n i k).le ⟨_, rfl⟩)
      exact hψ'
    · refine absurd ?_
        (show ProjSpace.ratio R p j l ∉ ((fstW ≫ (chartIso R n p i j).hom
          ≫ Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight (R := R)).toRingHom)).base w).asIdeal
          from by
            rw [← hηy_fst, Scheme.Hom.comp_apply]
            exact (range_SpecMap_awayMap R p j l).le ⟨_, rfl⟩)
      exact hψ'
  let ηz' := IsOpenImmersion.lift _ _ hrange
  have hstar1 : ηz' ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ᶻ
      (ProjSpace.X_mem_one R N (idx n p (k, l))) rfl)) = φ_ij :=
    IsOpenImmersion.lift_fac _ _ hrange
  let W := pullback ((prodCover R n p).f (i, j))
    ((prodCover R n p).f (k, l))
  let adj : ∀ {A : Type u} [CommRing A], (W ⟶ Spec (.of A)) → (A →+* Γ(W, ⊤)) :=
    fun {A} _ h => ((Scheme.ΓSpecIso (.of A)).inv ≫ h.appTop).hom
  have adj_comp : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
      (h : W ⟶ Spec (.of B)),
      adj (h ≫ Spec.map (CommRingCat.ofHom φ)) = (adj h).comp φ := fun {A B} _ _ φ h => by
    change ((Scheme.ΓSpecIso (.of A)).inv
      ≫ (Spec.map (CommRingCat.ofHom φ)).appTop ≫ h.appTop).hom = _
    rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  let τ := adj (fstW ≫ (chartIso R n p i j).hom)
  let ρ₁ := adj (sndW ≫ (chartIso R n p k l).hom)
  have hX : ∀ a, ρ₁ (ProjSpace.ratio R n k a ⊗ₜ[R] (1 : Away 𝒜ʸ (X l)))
      * τ (ProjSpace.ratio R n i k ⊗ₜ[R] (1 : Away 𝒜ʸ (X j)))
      = τ (ProjSpace.ratio R n i a ⊗ₜ[R] (1 : Away 𝒜ʸ (X j))) := fun a => by
    have := congrArg (adj ηx') (awayMap_ratio_transition R n i k a)
    rw [map_mul] at this
    have h1 : ∀ r, adj ηx' (HomogeneousLocalization.awayMap 𝒜ˣ
        (ProjSpace.X_mem_one R n k) rfl r) = τ (r ⊗ₜ[R] 1) := fun r =>
      (RingHom.congr_fun ((adj_comp _ ηx').symm.trans (congrArg adj hηx_fst)) r).trans
        (by rw [← Category.assoc, adj_comp]; rfl)
    have h2 : ∀ r, adj ηx' (HomogeneousLocalization.awayMap 𝒜ˣ
        (ProjSpace.X_mem_one R n i) (mul_comm _ _) r) = ρ₁ (r ⊗ₜ[R] 1) := fun r =>
      (RingHom.congr_fun ((adj_comp _ ηx').symm.trans (congrArg adj hηx_snd)) r).trans
        (by rw [← Category.assoc, adj_comp]; rfl)
    rw [h2, h1, h1] at this; exact this
  have hY : ∀ b, ρ₁ ((1 : Away 𝒜ˣ (X k)) ⊗ₜ[R] ProjSpace.ratio R p l b)
      * τ ((1 : Away 𝒜ˣ (X i)) ⊗ₜ[R] ProjSpace.ratio R p j l)
      = τ ((1 : Away 𝒜ˣ (X i)) ⊗ₜ[R] ProjSpace.ratio R p j b) := fun b => by
    have := congrArg (adj ηy') (awayMap_ratio_transition R p j l b)
    rw [map_mul] at this
    have h1 : ∀ r, adj ηy' (HomogeneousLocalization.awayMap 𝒜ʸ
        (ProjSpace.X_mem_one R p l) rfl r) = τ ((1 : Away 𝒜ˣ (X i)) ⊗ₜ[R] r) := fun r =>
      (RingHom.congr_fun ((adj_comp _ ηy').symm.trans (congrArg adj hηy_fst)) r).trans
        (by rw [← Category.assoc, adj_comp]; rfl)
    have h2 : ∀ r, adj ηy' (HomogeneousLocalization.awayMap 𝒜ʸ
        (ProjSpace.X_mem_one R p j) (mul_comm _ _) r) = ρ₁ ((1 : Away 𝒜ˣ (X k)) ⊗ₜ[R] r) :=
      fun r =>
        (RingHom.congr_fun ((adj_comp _ ηy').symm.trans (congrArg adj hηy_snd)) r).trans
          (by rw [← Category.assoc, adj_comp]; rfl)
    rw [h2, h1, h1] at this; exact this
  have hξ : ∀ r, adj ηz' (HomogeneousLocalization.awayMap 𝒜ᶻ
      (ProjSpace.X_mem_one R N (idx n p (k, l))) rfl r)
      = τ (segreChart R n p i j r) := fun r =>
    (RingHom.congr_fun ((adj_comp _ ηz').symm.trans (congrArg adj hstar1)) r).trans
      (RingHom.congr_fun (adj_comp _ _) r)
  have hstar2 : ηz' ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ᶻ
      (ProjSpace.X_mem_one R N (idx n p (i, j)))
      (mul_comm _ _))) = φ_kl := by
    refine ext_to_Spec ?_
    refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
    change adj (ηz' ≫ Spec.map _) z = adj φ_kl z
    rw [adj_comp, hφkl, adj_comp]
    change adj ηz' (HomogeneousLocalization.awayMap 𝒜ᶻ _ (mul_comm _ _) z)
      = ρ₁ (segreChart R n p k l z)
    have hz : z ∈ Algebra.adjoin R (Set.range (ProjSpace.ratio R N
        (idx n p (k, l)))) := by
      rw [ProjSpace.adjoin_range_ratio]; exact Algebra.mem_top
    induction hz using Algebra.adjoin_induction with
    | add a b _ _ ha hb => simp only [map_add, ha, hb]
    | mul a b _ _ ha hb => simp only [map_mul, ha, hb]
    | algebraMap r =>
        rw [segreChart_algebraMap,
          show ((1 : Away 𝒜ˣ (X k)) ⊗ₜ[R] algebraMap R (Away 𝒜ʸ (X l)) r : Away 𝒜ˣ (X k) ⊗[R] _)
            = (Algebra.TensorProduct.includeRight (R := R)).toRingHom (algebraMap R _ r) from rfl,
          show ρ₁ ((Algebra.TensorProduct.includeRight (R := R)).toRingHom
              (algebraMap R (Away 𝒜ʸ (X l)) r))
            = adj ηy' (HomogeneousLocalization.awayMap 𝒜ʸ
              (ProjSpace.X_mem_one R p j) (mul_comm _ _) (algebraMap R _ r)) from
            ((RingHom.congr_fun ((adj_comp _ ηy').symm.trans (congrArg adj hηy_snd)) _).trans
              (by rw [← Category.assoc, adj_comp]; rfl)).symm]
        rw [show HomogeneousLocalization.awayMap 𝒜ᶻ (ProjSpace.X_mem_one R N _)
              (mul_comm _ _) (algebraMap R _ r)
            = HomogeneousLocalization.awayMap 𝒜ᶻ (ProjSpace.X_mem_one R N
              (idx n p (k, l))) rfl (algebraMap R _ r) from by
          change HomogeneousLocalization.awayMap 𝒜ᶻ _ _
              (HomogeneousLocalization.fromZeroRingHom _ _ (ProjSpace.grad0Equiv R N r)) = _
          rw [HomogeneousLocalization.awayMap_fromZeroRingHom,
            ← HomogeneousLocalization.awayMap_fromZeroRingHom _
              (ProjSpace.X_mem_one R N (idx n p (k, l))) rfl]
          rfl,
          hξ, segreChart_algebraMap,
          show ((1 : Away 𝒜ˣ (X i)) ⊗ₜ[R] algebraMap R (Away 𝒜ʸ (X j)) r : Away 𝒜ˣ (X i) ⊗[R] _)
            = (Algebra.TensorProduct.includeRight (R := R)).toRingHom (algebraMap R _ r) from rfl,
          show τ ((Algebra.TensorProduct.includeRight (R := R)).toRingHom
              (algebraMap R (Away 𝒜ʸ (X j)) r))
            = adj ηy' (HomogeneousLocalization.awayMap 𝒜ʸ
              (ProjSpace.X_mem_one R p l) rfl (algebraMap R _ r)) from
            ((RingHom.congr_fun ((adj_comp _ ηy').symm.trans (congrArg adj hηy_fst)) _).trans
              (by rw [← Category.assoc, adj_comp]; rfl)).symm]
        congr 1
        change HomogeneousLocalization.awayMap 𝒜ʸ _ _
            (HomogeneousLocalization.fromZeroRingHom _ _ (ProjSpace.grad0Equiv R p r)) = _
        rw [HomogeneousLocalization.awayMap_fromZeroRingHom,
          ← HomogeneousLocalization.awayMap_fromZeroRingHom _
            (ProjSpace.X_mem_one R p j) (mul_comm _ _)]
        rfl
    | mem z hzm =>
        obtain ⟨β, rfl⟩ := hzm
        obtain ⟨⟨a, b⟩, rfl⟩ := (idx n p).surjective β
        have hT := congrArg (adj ηz') (awayMap_ratio_transition R N
          (idx n p (i, j)) (idx n p (k, l))
          (idx n p (a, b)))
        rw [map_mul, hξ, hξ, segreChart_ratio,
          segreChart_ratio] at hT
        rw [segreChart_ratio]
        have hXY : ρ₁ (ProjSpace.ratio R n k a ⊗ₜ[R] ProjSpace.ratio R p l b)
            * τ (ProjSpace.ratio R n i k ⊗ₜ[R] ProjSpace.ratio R p j l)
            = τ (ProjSpace.ratio R n i a ⊗ₜ[R] ProjSpace.ratio R p j b) := by
          have := mul_mul_mul_comm
            (ρ₁ (ProjSpace.ratio R n k a ⊗ₜ[R] (1 : Away 𝒜ʸ (X l))))
            (ρ₁ ((1 : Away 𝒜ˣ (X k)) ⊗ₜ[R] ProjSpace.ratio R p l b))
            (τ (ProjSpace.ratio R n i k ⊗ₜ[R] (1 : Away 𝒜ʸ (X j))))
            (τ ((1 : Away 𝒜ˣ (X i)) ⊗ₜ[R] ProjSpace.ratio R p j l))
          rw [hX a, hY b, ← map_mul, ← map_mul, ← map_mul,
            Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_one,
            one_mul, mul_one, one_mul] at this
          exact this
        have hunit : IsUnit (τ (ProjSpace.ratio R n i k
            ⊗ₜ[R] ProjSpace.ratio R p j l)) := by
          have hux := hX i
          rw [ProjSpace.ratio_self, ← Algebra.TensorProduct.one_def, map_one] at hux
          have huy := hY j
          rw [ProjSpace.ratio_self, ← Algebra.TensorProduct.one_def, map_one] at huy
          have : τ (ProjSpace.ratio R n i k ⊗ₜ[R] ProjSpace.ratio R p j l)
              = τ (ProjSpace.ratio R n i k ⊗ₜ[R] (1 : Away 𝒜ʸ (X j)))
              * τ ((1 : Away 𝒜ˣ (X i)) ⊗ₜ[R] ProjSpace.ratio R p j l) := by
            rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
          rw [this]
          exact (IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans hux)).mul
            (IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans huy))
        exact hunit.mul_right_cancel (hT.trans hXY.symm)
  rw [← hstar1, ← hstar2, Category.assoc, Category.assoc]
  erw [Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι]

/-- The Segre morphism from the fibre product of projective `n`- and
`p`-space over `Spec R` to projective `bigN n p`-space, glued from charts. -/
def segre2 :
    pullback (ProjSpace.π R n) (ProjSpace.π R p) ⟶ Proj 𝒜ᶻ :=
  (prodCover R n p).glueMorphisms
    (fun ij => chartMap R n p ij.1 ij.2)
    (chartMap_compat R n p)

theorem segre2_over :
    segre2 R n p ≫ ProjSpace.π R N
      = pullback.fst _ _ ≫ ProjSpace.π R n := by
  refine (prodCover R n p).hom_ext _ _ (fun ij => ?_)
  rw [segre2, ← Category.assoc, Scheme.Cover.ι_glueMorphisms]
  exact chartMap_over R n p ij

set_option maxHeartbeats 800000 in
-- Gluing the chart maps elaborates large pullback and localization terms.
theorem segre2_preimage (i : Fin (n + 1)) (j : Fin (p + 1)) :
    segre2 R n p
        ⁻¹ᵁ (Proj.awayι 𝒜ᶻ (X (idx n p (i, j)))
          (ProjSpace.X_mem_one R N _) one_pos).opensRange
      = ((prodCover R n p).f (i, j)).opensRange := by
  rw [Proj.opensRange_awayι, opensRange_prodCover_f,
    Proj.opensRange_awayι, Proj.opensRange_awayι]
  have hchart : ∀ (k : Fin (n + 1)) (l : Fin (p + 1)),
      (prodCover R n p).f (k, l)
        ⁻¹ᵁ (segre2 R n p
          ⁻¹ᵁ Proj.basicOpen 𝒜ᶻ (X (idx n p (i, j))))
      = (prodCover R n p).f (k, l)
        ⁻¹ᵁ (pullback.fst (ProjSpace.π R n) (ProjSpace.π R p)
            ⁻¹ᵁ Proj.basicOpen 𝒜ˣ (X i)
          ⊓ pullback.snd (ProjSpace.π R n) (ProjSpace.π R p)
            ⁻¹ᵁ Proj.basicOpen 𝒜ʸ (X j)) := fun k l => by
    rw [segre2,
      ← Scheme.Hom.comp_preimage ((prodCover R n p).f (k, l))
        ((prodCover R n p).glueMorphisms _ _),
      (prodCover R n p).ι_glueMorphisms _ _ (k, l)]
    change chartMap R n p k l ⁻¹ᵁ _ = _
    rw [chartMap, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
      Proj.awayι_preimage_basicOpen 𝒜ᶻ (ProjSpace.X_mem_one R N _) one_pos
        (ProjSpace.X_mem_one R N (idx n p (i, j))) one_pos,
      isLocElem_ratio]
    have hpf : (prodCover R n p).f (k, l)
          ⁻¹ᵁ (pullback.fst (ProjSpace.π R n) (ProjSpace.π R p)
            ⁻¹ᵁ Proj.basicOpen 𝒜ˣ (X i))
        = ((chartIso R n p k l).hom
            ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
          ⁻¹ᵁ PrimeSpectrum.basicOpen (ProjSpace.ratio R n k i) := by
      rw [chartIso_incL, ← isLocElem_ratio R n k i,
        ← Proj.awayι_preimage_basicOpen 𝒜ˣ (ProjSpace.X_mem_one R n k) one_pos
          (ProjSpace.X_mem_one R n i) one_pos,
        ← Scheme.Hom.comp_preimage]
      exact congrArg (· ⁻¹ᵁ _) (prodCover_fst R n p (k, l))
    have hps : (prodCover R n p).f (k, l)
          ⁻¹ᵁ (pullback.snd (ProjSpace.π R n) (ProjSpace.π R p)
            ⁻¹ᵁ Proj.basicOpen 𝒜ʸ (X j))
        = ((chartIso R n p k l).hom
            ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
              (R := R)).toRingHom))
          ⁻¹ᵁ PrimeSpectrum.basicOpen (ProjSpace.ratio R p l j) := by
      rw [chartIso_incR, ← isLocElem_ratio R p l j,
        ← Proj.awayι_preimage_basicOpen 𝒜ʸ (ProjSpace.X_mem_one R p l) one_pos
          (ProjSpace.X_mem_one R p j) one_pos,
        ← Scheme.Hom.comp_preimage]
      exact congrArg (· ⁻¹ᵁ _) (prodCover_snd R n p (k, l))
    rw [show (prodCover R n p).f (k, l) ⁻¹ᵁ (_ ⊓ _)
        = (prodCover R n p).f (k, l) ⁻¹ᵁ _
          ⊓ (prodCover R n p).f (k, l) ⁻¹ᵁ _ from rfl, hpf, hps,
      Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
    rw [show (_ ⁻¹ᵁ _ ⊓ _ ⁻¹ᵁ _ : ((prodCover R n p).X (k, l)).Opens)
        = (chartIso R n p k l).hom ⁻¹ᵁ (_ ⊓ _) from rfl]
    congr 1
    erw [← PrimeSpectrum.basicOpen_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
      ← segreChart_ratio R n p k l i j]
    rfl
  have hcov := (prodCover R n p).iSup_opensRange
  refine le_antisymm (fun q hq => ?_) (fun q hq => ?_)
  all_goals
    obtain ⟨⟨k, l⟩, q', rfl⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (show q ∈ ⨆ α, ((prodCover R n p).f α).opensRange from hcov.ge trivial)
  · exact (hchart k l).le hq
  · exact (hchart k l).ge hq

set_option maxHeartbeats 800000 in
-- Gluing the chart maps elaborates large pullback and localization terms.
theorem segre2_closedImm :
    IsClosedImmersion (segre2 R n p) := by
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
    (𝒰 := (ProjSpace.affineOpenCover R N).openCover) (fun β => ?_)
  dsimp only [Scheme.Cover.pullbackHom]
  obtain ⟨⟨i, j⟩, hβ⟩ := (idx n p).surjective β
  subst hβ
  have hrange : Set.range ((prodCover R n p).f (i, j)).base
      = Set.range (pullback.fst (segre2 R n p)
        ((ProjSpace.affineOpenCover R N).openCover.f (idx n p (i, j)))).base := by
    have := segre2_preimage R n p i j
    rw [← Scheme.Hom.opensRange_pullbackFst] at this
    exact congrArg SetLike.coe this.symm
  let e := IsOpenImmersion.isoOfRangeEq ((prodCover R n p).f (i, j))
    (pullback.fst _ _) hrange
  have hθcond : (prodCover R n p).f (i, j) ≫ segre2 R n p
      = ((chartIso R n p i j).hom
          ≫ Spec.map (CommRingCat.ofHom (segreChart R n p i j)))
        ≫ (ProjSpace.affineOpenCover R N).openCover.f (idx n p (i, j)) := by
    rw [segre2, (prodCover R n p).ι_glueMorphisms _ _ (i, j),
      Category.assoc, ProjSpace.affineOpenCover_f]
    rfl
  let θ := pullback.lift ((prodCover R n p).f (i, j))
    ((chartIso R n p i j).hom
      ≫ Spec.map (CommRingCat.ofHom (segreChart R n p i j))) hθcond
  have hsnd : e.hom ≫ pullback.snd (segre2 R n p)
        ((ProjSpace.affineOpenCover R N).openCover.f (idx n p (i, j)))
      = (chartIso R n p i j).hom
        ≫ Spec.map (CommRingCat.ofHom (segreChart R n p i j)) := by
    rw [show e.hom = θ from (cancel_mono (pullback.fst _ _)).mp
      ((IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).trans (pullback.lift_fst _ _ _).symm)]
    exact pullback.lift_snd _ _ _
  have hci : IsClosedImmersion (e.hom ≫ pullback.snd (segre2 R n p)
      ((ProjSpace.affineOpenCover R N).openCover.f (idx n p (i, j)))) := by
    rw [hsnd]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
      (chartIso R n p i j).hom _).mpr
      (IsClosedImmersion.spec_of_surjective _ (segreChart_surjective R n p i j))
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) e.hom _).mp hci

end ProductCover

section Recursive

variable (R : Type u) [CommRing R]

/-- A closed immersion over `Spec R` of `prodOver R e` into some projective
space. -/
structure SegreDatum {m : ℕ} (e : Fin m → ℕ) where

/-- The dimension of the target projective space. -/
  Nd : ℕ

/-- The embedding. -/
  segσ : ProjSpace.prodOver R e
    ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (Nd + 1)) R)

/-- The embedding is a closed immersion. -/
  hσ_closed : IsClosedImmersion segσ

/-- The embedding commutes with the structure morphisms. -/
  hσ_over : segσ ≫ ProjSpace.π R Nd = ProjSpace.prodOverπ R e

attribute [scoped instance] SegreDatum.hσ_closed

/-- Evaluation at `X 0 = 1`, identifying projective `0`-space with `Spec R`. -/
def eval0 : MvPolynomial (Fin (0 + 1)) R →+* Γ(Spec (.of R), ⊤) :=
  (Scheme.ΓSpecIso (.of R)).inv.hom.comp
    ((MvPolynomial.aeval (R := R) (fun _ => (1 : R))).toRingHom)

theorem eval0_irrelevant :
    (HomogeneousIdeal.irrelevant
      (homogeneousSubmodule (Fin (0 + 1)) R)).toIdeal.map (eval0 R) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have hX0 : eval0 R (X 0) = 1 := by
    unfold eval0
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      MvPolynomial.aeval_X]
    exact map_one _
  rw [← hX0]
  refine Ideal.mem_map_of_mem _ ?_
  exact (HomogeneousIdeal.mem_irrelevant_iff _ _).mpr
    (DirectSum.decompose_of_mem_ne _ (ProjSpace.X_mem_one R 0 0) one_ne_zero)

theorem eval0_grad0 :
    ((eval0 R).comp
        (algebraMap ((homogeneousSubmodule (Fin (0 + 1)) R) 0)
          (MvPolynomial (Fin (0 + 1)) R))).comp
      (ProjSpace.grad0Equiv R 0).toRingHom
      = (Scheme.ΓSpecIso (.of R)).inv.hom := by
  ext r
  change (eval0 R) (algebraMap _ _ ((ProjSpace.grad0Equiv R 0) r)) = _
  have hval : (algebraMap ((homogeneousSubmodule (Fin (0 + 1)) R) 0)
      (MvPolynomial (Fin (0 + 1)) R)) ((ProjSpace.grad0Equiv R 0) r) = MvPolynomial.C r := rfl
  rw [hval, eval0, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, MvPolynomial.aeval_C]
  rfl

theorem segreAux0_section :
    Proj.fromOfGlobalSections (homogeneousSubmodule (Fin (0 + 1)) R)
        (eval0 R) (eval0_irrelevant R)
      ≫ ProjSpace.π R 0 = 𝟙 (Spec (.of R)) := by
  rw [ProjSpace.π, ← Category.assoc, Proj.fromOfGlobalSections_toSpecZero,
    Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    eval0_grad0, CommRingCat.ofHom_hom]
  exact toSpecΓ_SpecMap_ΓSpecIso_inv (.of R)

/-- The empty product embeds as projective `0`-space. -/
def segreAux0 : SegreDatum R (Fin.elim0 : Fin 0 → ℕ) where
  Nd := 0
  segσ := Proj.fromOfGlobalSections (homogeneousSubmodule (Fin (0 + 1)) R)
    (eval0 R) (eval0_irrelevant R)
  hσ_closed := by
    have hsep : IsSeparated (ProjSpace.π R 0) :=
      (ProjSpace.isProper_π R 0).toIsSeparated
    have hcomp : IsClosedImmersion (Proj.fromOfGlobalSections (homogeneousSubmodule (Fin (0 + 1)) R)
        (eval0 R) (eval0_irrelevant R)
        ≫ ProjSpace.π R 0) := by
      rw [segreAux0_section R]; infer_instance
    exact @IsClosedImmersion.of_comp _ _ _ _ (ProjSpace.π R 0) hcomp hsep
  hσ_over := by
    change _ = 𝟙 (Spec (.of R))
    exact segreAux0_section R

/-- Inductive step: base change of an embedding of the tail, followed by
`segre2`. -/
def segreAuxSucc {m : ℕ} (e : Fin (m + 1) → ℕ)
    (ih : SegreDatum R (e ∘ Fin.succ)) : SegreDatum R e where
  Nd := bigN (e 0) ih.Nd
  segσ :=
    pullback.map _ _ _ _ (𝟙 _) ih.segσ (𝟙 _) (by simp) (by simp [ih.hσ_over])
    ≫ segre2 R (e 0) ih.Nd
  hσ_closed := by
    have : IsClosedImmersion (pullback.map (ProjSpace.π R (e 0))
        (ProjSpace.prodOverπ R (e ∘ Fin.succ)) (ProjSpace.π R (e 0))
        (ProjSpace.π R ih.Nd) (𝟙 _) ih.segσ (𝟙 _) (by simp)
        (by simp [ih.hσ_over])) := by
      refine MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @IsClosedImmersion)
        (f := pullback.snd (ProjSpace.π R (e 0)) (ProjSpace.π R ih.Nd))
        (f' := pullback.snd _ _) ?_ ih.hσ_closed
      refine (IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
        (IsPullback.of_hasPullback (ProjSpace.π R (e 0)) (ProjSpace.π R ih.Nd))).flip
      rw [pullback.lift_fst, Category.comp_id, ih.hσ_over]
      exact IsPullback.of_hasPullback _ _
    exact MorphismProperty.IsStableUnderComposition.comp_mem _ _ this
      (segre2_closedImm R (e 0) ih.Nd)
  hσ_over := by
    rw [Category.assoc, segre2_over]
    change pullback.map _ _ _ _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ _
      = pullback.fst _ _ ≫ ProjSpace.π R (e 0)
    rw [← Category.assoc, pullback.lift_fst, Category.comp_id]

/-- The iterated Segre embedding of `prodOver R e` into projective space. -/
def segreAux : ∀ {m : ℕ} (e : Fin m → ℕ), SegreDatum R e
  | 0, e => (funext (fun k => k.elim0) : e = Fin.elim0) ▸ segreAux0 R
  | _ + 1, e => segreAuxSucc R e (segreAux (e ∘ Fin.succ))

end Recursive

end ProjSpace.Segre

end AlgebraicGeometry
