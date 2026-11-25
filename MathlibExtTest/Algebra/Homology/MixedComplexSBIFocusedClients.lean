/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Algebra.Homology.MixedComplex.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Ring.Rat
import Mathlib.LinearAlgebra.Prod
import MathlibExt.Algebra.Homology.SBISequence
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Focused clients of mixed complexes

A concrete mixed complex in `ModuleCat ℚ` with carrier `ℚ × ℚ` in every degree. Write `xₙ, yₙ`
for the standard basis in degree `n`. The nonzero structure maps are

* `d 1 0 (a, b) = (b, 0)` and `d 2 1 (a, b) = (-a, 0)`;
* `B 0 (a, b) = (a, 0)` and `B 1 (a, b) = (b, 0)`.

All other differentials and mixed operators vanish. The axioms hold for real reasons:

* `B 0 ≫ d 1 0 = 0` because the image of `B 0` is the `x`-line, which is the kernel of `d 1 0`;
  both factors are nonzero.
* The degree-zero anticommutation `B 1 ≫ d 2 1 + d 1 0 ≫ B 0 = 0` cancels two nonzero
  summands, `(a, b) ↦ (-b, 0)` and `(a, b) ↦ (b, 0)`, by sign.

The morphism `diag` is the projection onto the indecomposable summand spanned by `y₁`, `x₀`,
`x₁`, `x₂`, and `side` is the projection onto `y₀`. Both are nonzero, neither is the identity, and
`B` is nonzero where their `B`-compatibility is checked. The file evaluates the forgetful
functor, uses its faithfulness, and computes sums, negatives, natural multiples, identities, and
composites of mixed-complex morphisms.

## SBI diagrams

The last section builds an exact connective `NatSBIDiagram` in `ModuleCat ℚ` with nonzero
periodicity and connecting maps meeting at the same object:

* `H 0 = HC 0 = ℚ²` with `I 0 = 𝟙`, `H 1 = ℚ`, and `H n = 0` for `n ≥ 2`;
* `HC (2k) = ℚ` and `HC (2k + 1) = 0` for `k ≥ 1`;
* `S 0 t = (t, 0)`, `B 0 (a, b) = b`, `S (n + 1) = 𝟙`, and all other maps vanish.

`S 0 ≫ B 0 = 0` although both maps are nonzero, and the three `Exact` fields and the
`ConnectiveBoundary` are proved in every degree: by a splitting at `HC 0`, by a split mono or
epi where the other map vanishes, and by a zero middle object elsewhere. The comparison
theorems `Hom.isIso_hcMap_of_isIso_hMap`, `Hom.isIso_hcMap_of_isIso_hMap_le` and
`Hom.isIso_hMap_iff_isIso_hcMap` are then applied to the negation endomorphism of this diagram.
This diagram is built directly; it is not computed from the mixed complex above.

Chain-level `ConnesSBIPresentation`s, which produce such diagrams, are exercised in
`MathlibExtTest/Algebra/Homology/ConnesSBIFocusedClients.lean`.
-/

open CategoryTheory

namespace MathlibExtTest.Algebra.Homology.MixedComplexSBIFocusedClients

/-- The carrier in every degree. -/
abbrev V : ModuleCat ℚ := ModuleCat.of ℚ (ℚ × ℚ)

/-- `(a, b) ↦ (a, 0)`. -/
abbrev keepFst : V ⟶ V := ModuleCat.ofHom (LinearMap.inl ℚ ℚ ℚ ∘ₗ LinearMap.fst ℚ ℚ ℚ)

/-- `(a, b) ↦ (b, 0)`. -/
abbrev sndToFst : V ⟶ V := ModuleCat.ofHom (LinearMap.inl ℚ ℚ ℚ ∘ₗ LinearMap.snd ℚ ℚ ℚ)

/-- `(a, b) ↦ (0, b)`. -/
abbrev keepSnd : V ⟶ V := ModuleCat.ofHom (LinearMap.inr ℚ ℚ ℚ ∘ₗ LinearMap.snd ℚ ℚ ℚ)

theorem V_hom_ext {f g : V ⟶ V} (h : ∀ x : ℚ × ℚ, f.hom x = g.hom x) : f = g :=
  ModuleCat.hom_ext (LinearMap.ext h)

/-- The differential `d (n + 1) n`. -/
def dmap : ℕ → (V ⟶ V)
  | 0 => sndToFst
  | 1 => -keepFst
  | _ + 2 => 0

/-- The mixed operator `B n`. -/
def Bmap : ℕ → (V ⟶ V)
  | 0 => keepFst
  | 1 => sndToFst
  | _ + 2 => 0

theorem dmap_comp (n : ℕ) : dmap (n + 1) ≫ dmap n = 0 := by
  rcases n with _ | n
  · apply V_hom_ext
    intro x
    simp [dmap]
  · change dmap (n + 2) ≫ dmap (n + 1) = 0
    rw [show dmap (n + 2) = 0 from rfl, Limits.zero_comp]

/-- The underlying chain complex. -/
abbrev chain : ChainComplex (ModuleCat ℚ) ℕ :=
  ChainComplex.of (fun _ => V) dmap dmap_comp

theorem chain_d (n : ℕ) : chain.d (n + 1) n = dmap n :=
  ChainComplex.of_d (fun _ => V) dmap n

theorem chain_d_succ (n : ℕ) : chain.d (n + 2) (n + 1) = dmap (n + 1) :=
  ChainComplex.of_d (fun _ => V) dmap (n + 1)

/-- The model mixed complex. Each axiom is discharged by computing on elements. -/
def mixed : MixedComplex (ModuleCat ℚ) where
  underlying := chain
  B := Bmap
  B_sq n := by
    rcases n with _ | _ | n
    · apply V_hom_ext
      intro x
      simp [Bmap]
    · change sndToFst ≫ 0 = 0
      exact Limits.comp_zero
    · change 0 ≫ Bmap (n + 3) = 0
      exact Limits.zero_comp
  B_b_zero := by
    rw [chain_d]
    apply V_hom_ext
    intro x
    simp [Bmap, dmap]
  anticomm n := by
    rw [chain_d_succ, chain_d]
    rcases n with _ | _ | n
    · apply V_hom_ext
      intro x
      simp [Bmap, dmap]
    · apply V_hom_ext
      intro x
      simp [Bmap, dmap]
    · change 0 ≫ dmap (n + 3) + dmap (n + 2) ≫ 0 = 0
      rw [Limits.zero_comp, Limits.comp_zero, add_zero]

theorem mixed_B (n : ℕ) : mixed.B n = Bmap n := rfl

theorem mixed_d (n : ℕ) : mixed.underlying.d (n + 1) n = dmap n := chain_d n

/-! ### Nonvanishing and the degree-zero boundary -/

theorem mixed_B_zero_apply (a b : ℚ) : (mixed.B 0).hom (a, b) = (a, 0) := rfl

theorem mixed_d_one_zero_apply (a b : ℚ) : (mixed.underlying.d 1 0).hom (a, b) = (b, 0) := by
  rw [mixed_d]
  rfl

theorem mixed_d_two_one_apply (a b : ℚ) :
    (mixed.underlying.d 2 1).hom (a, b) = (-a, 0) := by
  rw [mixed_d]
  rfl

theorem mixed_B_zero_ne_zero : mixed.B 0 ≠ 0 := by
  intro h
  have h₁ := congrArg (fun f : V ⟶ V => f.hom ((1 : ℚ), (0 : ℚ))) h
  change keepFst.hom ((1 : ℚ), (0 : ℚ)) = (0 : V ⟶ V).hom ((1 : ℚ), (0 : ℚ)) at h₁
  simp at h₁

theorem mixed_B_one_ne_zero : mixed.B 1 ≠ 0 := by
  intro h
  have h₁ := congrArg (fun f : V ⟶ V => f.hom ((0 : ℚ), (1 : ℚ))) h
  change sndToFst.hom ((0 : ℚ), (1 : ℚ)) = (0 : V ⟶ V).hom ((0 : ℚ), (1 : ℚ)) at h₁
  simp at h₁

theorem mixed_d_one_zero_ne_zero : mixed.underlying.d 1 0 ≠ 0 := by
  rw [mixed_d]
  intro h
  have h₁ := congrArg (fun f : V ⟶ V => f.hom ((0 : ℚ), (1 : ℚ))) h
  change sndToFst.hom ((0 : ℚ), (1 : ℚ)) = (0 : V ⟶ V).hom ((0 : ℚ), (1 : ℚ)) at h₁
  simp at h₁

theorem mixed_d_two_one_ne_zero : mixed.underlying.d 2 1 ≠ 0 := by
  rw [mixed_d]
  intro h
  have h₁ := congrArg (fun f : V ⟶ V => f.hom ((1 : ℚ), (0 : ℚ))) h
  change (-keepFst).hom ((1 : ℚ), (0 : ℚ)) = (0 : V ⟶ V).hom ((1 : ℚ), (0 : ℚ)) at h₁
  simp at h₁

/-- The image of `B 0` lies in the kernel of `d 1 0`, and `B 0` reaches that kernel's
generator `(1, 0)`, so the boundary equation is not a vanishing factor. -/
theorem degree_zero_boundary :
    (∀ x : ℚ × ℚ, (mixed.underlying.d 1 0).hom ((mixed.B 0).hom x) = 0) ∧
      (mixed.B 0).hom ((1 : ℚ), (0 : ℚ)) = ((1 : ℚ), (0 : ℚ)) ∧
      (mixed.underlying.d 1 0).hom ((1 : ℚ), (0 : ℚ)) = 0 := by
  refine ⟨fun x => ?_, rfl, ?_⟩
  · rw [mixed_d]
    rfl
  · rw [mixed_d_one_zero_apply]
    rfl

/-- The degree-zero anticommutation cancels two nonzero summands. -/
theorem anticomm_zero_summands :
    (mixed.B 1 ≫ mixed.underlying.d 2 1).hom ((0 : ℚ), (1 : ℚ)) = ((-1 : ℚ), (0 : ℚ)) ∧
      (mixed.underlying.d 1 0 ≫ mixed.B 0).hom ((0 : ℚ), (1 : ℚ)) = ((1 : ℚ), (0 : ℚ)) ∧
      mixed.B 1 ≫ mixed.underlying.d 2 1 + mixed.underlying.d 1 0 ≫ mixed.B 0 = 0 := by
  refine ⟨?_, ?_, mixed.anticomm 0⟩
  · rw [mixed_d]
    change (sndToFst ≫ (-keepFst)).hom ((0 : ℚ), (1 : ℚ)) = ((-1 : ℚ), (0 : ℚ))
    simp
  · rw [mixed_d]
    change (sndToFst ≫ keepFst).hom ((0 : ℚ), (1 : ℚ)) = ((1 : ℚ), (0 : ℚ))
    simp

/-! ### Morphisms -/

/-- Components of the projection onto the indecomposable summand. -/
def diagMap : ℕ → (V ⟶ V)
  | 0 => keepFst
  | 1 => 𝟙 V
  | 2 => keepFst
  | _ + 3 => 0

/-- Components of the projection onto the isolated generator `y₀`. -/
def sideMap : ℕ → (V ⟶ V)
  | 0 => keepSnd
  | _ + 1 => 0

/-- The projection onto the indecomposable summand. -/
def diag : mixed ⟶ mixed where
  underlying := ChainComplex.ofHom (X := chain) (Y := chain) diagMap (fun i => by
    rw [chain_d]
    rcases i with _ | _ | _ | i
    · change 𝟙 V ≫ sndToFst = sndToFst ≫ keepFst
      apply V_hom_ext
      intro x
      simp
    · change keepFst ≫ (-keepFst) = (-keepFst) ≫ 𝟙 V
      apply V_hom_ext
      intro x
      simp
    · change (0 : V ⟶ V) ≫ 0 = 0 ≫ keepFst
      rw [Limits.zero_comp, Limits.zero_comp]
    · change (0 : V ⟶ V) ≫ 0 = 0 ≫ 0
      rfl)
  comm_B' n := by
    rcases n with _ | _ | _ | n
    · change keepFst ≫ keepFst = keepFst ≫ 𝟙 V
      apply V_hom_ext
      intro x
      simp
    · change 𝟙 V ≫ sndToFst = sndToFst ≫ keepFst
      apply V_hom_ext
      intro x
      simp
    · change keepFst ≫ 0 = 0 ≫ (0 : V ⟶ V)
      rw [Limits.comp_zero, Limits.zero_comp]
    · change (0 : V ⟶ V) ≫ 0 = 0 ≫ 0
      rfl

/-- The projection onto the isolated generator `y₀`. -/
def side : mixed ⟶ mixed where
  underlying := ChainComplex.ofHom (X := chain) (Y := chain) sideMap (fun i => by
    rw [chain_d]
    rcases i with _ | i
    · change (0 : V ⟶ V) ≫ sndToFst = sndToFst ≫ keepSnd
      apply V_hom_ext
      intro x
      rfl
    · change (0 : V ⟶ V) ≫ dmap (i + 1) = dmap (i + 1) ≫ 0
      rw [Limits.zero_comp, Limits.comp_zero])
  comm_B' n := by
    rcases n with _ | n
    · change keepSnd ≫ keepFst = keepFst ≫ (0 : V ⟶ V)
      apply V_hom_ext
      intro x
      simp
    · change (0 : V ⟶ V) ≫ Bmap (n + 1) = Bmap (n + 1) ≫ 0
      rw [Limits.zero_comp, Limits.comp_zero]

theorem diag_f (n : ℕ) : diag.underlying.f n = diagMap n := rfl

theorem side_f (n : ℕ) : side.underlying.f n = sideMap n := rfl

/-- `comm_B` for `diag` in degree one, where `B 1 ≠ 0` and both sides are nonzero. -/
theorem diag_comm_B_one :
    (diag.underlying.f 1 ≫ mixed.B 1).hom ((0 : ℚ), (1 : ℚ)) = ((1 : ℚ), (0 : ℚ)) ∧
      diag.underlying.f 1 ≫ mixed.B 1 = mixed.B 1 ≫ diag.underlying.f 2 := by
  refine ⟨?_, diag.comm_B 1⟩
  change (𝟙 V ≫ sndToFst).hom ((0 : ℚ), (1 : ℚ)) = ((1 : ℚ), (0 : ℚ))
  simp

/-- The forgetful functor sends `diag` to its chain map, which is the identity in degree one
and kills `y` in degree zero. -/
theorem underlyingFunctor_map_diag :
    ((MixedComplex.underlyingFunctor (ModuleCat ℚ)).map diag).f 1 = 𝟙 V ∧
      (((MixedComplex.underlyingFunctor (ModuleCat ℚ)).map diag).f 0).hom
        ((0 : ℚ), (1 : ℚ)) = 0 := by
  rw [MixedComplex.underlyingFunctor_map]
  exact ⟨rfl, rfl⟩

theorem diag_ne_zero : diag ≠ 0 := by
  intro h
  have h₁ := congrArg (fun f : mixed ⟶ mixed => (f.underlying.f 1 : V ⟶ V)) h
  change 𝟙 V = 0 at h₁
  have h₂ := congrArg (fun f : V ⟶ V => f.hom ((1 : ℚ), (0 : ℚ))) h₁
  simp at h₂

theorem diag_ne_id : diag ≠ 𝟙 mixed := by
  intro h
  have h₁ := congrArg (fun f : mixed ⟶ mixed => (f.underlying.f 0 : V ⟶ V)) h
  change keepFst = 𝟙 V at h₁
  have h₂ := congrArg (fun f : V ⟶ V => f.hom ((0 : ℚ), (1 : ℚ))) h₁
  simp at h₂

/-- The two morphisms have different chain maps under the forgetful functor. -/
theorem underlyingFunctor_map_diag_ne_side :
    (MixedComplex.underlyingFunctor (ModuleCat ℚ)).map diag ≠
      (MixedComplex.underlyingFunctor (ModuleCat ℚ)).map side := by
  rw [MixedComplex.underlyingFunctor_map, MixedComplex.underlyingFunctor_map]
  intro h
  have h₁ := congrArg (fun f : mixed.underlying ⟶ mixed.underlying => (f.f 1 : V ⟶ V)) h
  change 𝟙 V = 0 at h₁
  have h₂ := congrArg (fun f : V ⟶ V => f.hom ((1 : ℚ), (0 : ℚ))) h₁
  simp at h₂

/-- Faithfulness turns a degreewise chain-map computation into an equality of mixed-complex
morphisms: `diag` is idempotent. -/
theorem diag_comp_diag : diag ≫ diag = diag := by
  apply (MixedComplex.underlyingFunctor (ModuleCat ℚ)).map_injective
  rw [Functor.map_comp, MixedComplex.underlyingFunctor_map]
  ext n : 1
  rw [HomologicalComplex.comp_f, diag_f]
  rcases n with _ | _ | _ | n
  · change keepFst ≫ keepFst = keepFst
    apply V_hom_ext
    intro x
    simp
  · exact Category.id_comp _
  · change keepFst ≫ keepFst = keepFst
    apply V_hom_ext
    intro x
    simp
  · exact Limits.zero_comp

/-- `comp_underlying` computes the composite of the two projections as zero. -/
theorem diag_comp_side : diag ≫ side = 0 := by
  apply MixedComplex.hom_ext
  rw [MixedComplex.comp_underlying, MixedComplex.zero_underlying]
  ext n : 1
  rw [HomologicalComplex.comp_f, diag_f, side_f, HomologicalComplex.zero_f]
  rcases n with _ | n
  · change keepFst ≫ keepSnd = 0
    apply V_hom_ext
    intro x
    simp
  · exact Limits.comp_zero

/-- `id_underlying` on an element. -/
theorem id_underlying_apply :
    ((𝟙 mixed : mixed ⟶ mixed).underlying.f 1).hom ((3 : ℚ), (5 : ℚ)) = ((3 : ℚ), (5 : ℚ)) := by
  rw [MixedComplex.id_underlying]
  rfl

/-! ### Additive structure -/

/-- The sum of the two projections is the identity in degree zero. -/
theorem add_underlying_zero : (diag + side).underlying.f 0 = 𝟙 V := by
  rw [MixedComplex.add_underlying, HomologicalComplex.add_f_apply, diag_f, side_f]
  change keepFst + keepSnd = 𝟙 V
  apply V_hom_ext
  intro x
  simp

/-- But the sum is not the identity: in degree three both projections vanish. -/
theorem add_ne_id : diag + side ≠ 𝟙 mixed := by
  intro h
  have h₁ := congrArg (fun f : mixed ⟶ mixed => (f.underlying.f 3 : V ⟶ V)) h
  rw [MixedComplex.add_underlying, MixedComplex.id_underlying, HomologicalComplex.add_f_apply,
    diag_f, side_f] at h₁
  change (0 : V ⟶ V) + 0 = 𝟙 V at h₁
  have h₂ := congrArg (fun f : V ⟶ V => f.hom ((1 : ℚ), (0 : ℚ))) h₁.symm
  simp at h₂

theorem neg_underlying_apply :
    ((-diag).underlying.f 1).hom ((2 : ℚ), (7 : ℚ)) = ((-2 : ℚ), (-7 : ℚ)) := by
  rw [MixedComplex.neg_underlying, HomologicalComplex.neg_f_apply, diag_f]
  change (-𝟙 V).hom ((2 : ℚ), (7 : ℚ)) = ((-2 : ℚ), (-7 : ℚ))
  simp

theorem nsmul_underlying_apply :
    ((2 • diag).underlying.f 0).hom ((3 : ℚ), (5 : ℚ)) = ((3 : ℚ) + 3, (0 : ℚ)) := by
  rw [MixedComplex.nsmul_underlying, HomologicalComplex.nsmul_f_apply, two_nsmul, diag_f]
  change (keepFst + keepFst).hom ((3 : ℚ), (5 : ℚ)) = ((3 : ℚ) + 3, (0 : ℚ))
  simp

/-! ### An exact connective SBI diagram -/

/-- The rank-one carrier. -/
abbrev L : ModuleCat ℚ := ModuleCat.of ℚ ℚ

/-- The zero carrier. -/
abbrev Z : ModuleCat ℚ := ModuleCat.of ℚ PUnit

theorem Z_isZero : Limits.IsZero Z := ModuleCat.isZero_of_subsingleton Z

/-- Ordinary homology: `ℚ²`, `ℚ`, then zero. -/
def sbiH : ℕ → ModuleCat ℚ
  | 0 => V
  | 1 => L
  | _ + 2 => Z

/-- Positive cyclic-type homology, `HC (n + 1)`: zero in even `n`, `ℚ` in odd `n`. -/
def sbiHCpos : ℕ → ModuleCat ℚ
  | 0 => Z
  | 1 => L
  | n + 2 => sbiHCpos n

/-- Cyclic-type homology. -/
def sbiHC : ℕ → ModuleCat ℚ
  | 0 => V
  | n + 1 => sbiHCpos n

/-- `t ↦ (t, 0)`. -/
abbrev inlL : L ⟶ V := ModuleCat.ofHom (LinearMap.inl ℚ ℚ ℚ)

/-- `t ↦ (0, t)`. -/
abbrev inrL : L ⟶ V := ModuleCat.ofHom (LinearMap.inr ℚ ℚ ℚ)

/-- `(a, b) ↦ a`. -/
abbrev fstL : V ⟶ L := ModuleCat.ofHom (LinearMap.fst ℚ ℚ ℚ)

/-- `(a, b) ↦ b`. -/
abbrev sndL : V ⟶ L := ModuleCat.ofHom (LinearMap.snd ℚ ℚ ℚ)

/-- The inclusion maps. -/
def sbiI : ∀ n : ℕ, sbiH n ⟶ sbiHC n
  | 0 => 𝟙 V
  | _ + 1 => 0

/-- The periodicity maps. -/
def sbiS : ∀ n : ℕ, sbiHC (n + 2) ⟶ sbiHC n
  | 0 => inlL
  | n + 1 => 𝟙 (sbiHCpos n)

/-- The connecting maps. -/
def sbiB : ∀ n : ℕ, sbiHC n ⟶ sbiH (n + 1)
  | 0 => sndL
  | _ + 1 => 0

theorem inlL_comp_sndL : inlL ≫ sndL = 0 :=
  ModuleCat.hom_ext (LinearMap.ext fun t => by simp)

/-- The model SBI diagram. -/
def sbi : NatSBIDiagram (A := ModuleCat ℚ) where
  H := sbiH
  HC := sbiHC
  I := sbiI
  S := sbiS
  B := sbiB
  S_comp_B n := by
    rcases n with _ | n
    · exact inlL_comp_sndL
    · exact Limits.comp_zero
  B_comp_I _ := Limits.comp_zero
  I_comp_S _ := Limits.zero_comp

theorem sbi_S_zero_apply (t : ℚ) : (sbi.S 0).hom t = (t, 0) := rfl

theorem sbi_B_zero_apply (a b : ℚ) : (sbi.B 0).hom (a, b) = b := rfl

theorem sbi_S_zero_ne_zero : sbi.S 0 ≠ 0 := by
  intro h
  have h₁ := congrArg (fun f : L ⟶ V => f.hom (1 : ℚ)) h
  change inlL.hom (1 : ℚ) = (0 : L ⟶ V).hom (1 : ℚ) at h₁
  simp at h₁

theorem sbi_B_zero_ne_zero : sbi.B 0 ≠ 0 := by
  intro h
  have h₁ := congrArg (fun f : V ⟶ L => f.hom ((0 : ℚ), (1 : ℚ))) h
  change sndL.hom ((0 : ℚ), (1 : ℚ)) = (0 : V ⟶ L).hom ((0 : ℚ), (1 : ℚ)) at h₁
  simp at h₁

/-- The composite `S 0 ≫ B 0` vanishes although both factors are nonzero: the image of
`S 0` is the kernel of `B 0`. -/
theorem sbi_S_comp_B_zero_nonvacuous :
    sbi.S 0 ≫ sbi.B 0 = 0 ∧ sbi.S 0 ≠ 0 ∧ sbi.B 0 ≠ 0 :=
  ⟨sbi.S_comp_B 0, sbi_S_zero_ne_zero, sbi_B_zero_ne_zero⟩

/-- The SBI diagram is exact in every degree. -/
theorem sbi_exact : sbi.Exact where
  exact_SB n := by
    rcases n with _ | n
    · exact ShortComplex.Splitting.exact
        { r := fstL
          s := inrL
          f_r := by
            change inlL ≫ fstL = 𝟙 L
            exact ModuleCat.hom_ext (LinearMap.ext fun t => by simp)
          s_g := by
            change inrL ≫ sndL = 𝟙 L
            exact ModuleCat.hom_ext (LinearMap.ext fun t => by simp)
          id := by
            change fstL ≫ inlL + sndL ≫ inrL = 𝟙 V
            exact V_hom_ext fun x => by simp }
    · refine (ShortComplex.exact_iff_epi _ rfl).2 ?_
      change Epi (𝟙 (sbiHCpos n))
      infer_instance
  exact_BI n := by
    rcases n with _ | n
    · refine (ShortComplex.exact_iff_epi _ rfl).2 ?_
      change Epi sndL
      exact epi_of_epi_fac
        (show inrL ≫ sndL = 𝟙 L from ModuleCat.hom_ext (LinearMap.ext fun t => by simp))
    · exact ShortComplex.exact_of_isZero_X₂ _ Z_isZero
  exact_IS n := by
    refine (ShortComplex.exact_iff_mono _ rfl).2 ?_
    rcases n with _ | n
    · change Mono inlL
      exact mono_of_mono_fac
        (show inlL ≫ fstL = 𝟙 L from ModuleCat.hom_ext (LinearMap.ext fun t => by simp))
    · change Mono (𝟙 (sbiHCpos n))
      infer_instance

theorem sbi_connective : sbi.ConnectiveBoundary where
  isIso_I_zero := by
    change IsIso (𝟙 V)
    infer_instance
  epi_I_one := Z_isZero.epi _

/-- Negation on both homology families is an endomorphism of any SBI diagram. -/
def negHom (D : NatSBIDiagram (A := ModuleCat ℚ)) : D ⟶ D where
  hMap _ := -𝟙 _
  hcMap _ := -𝟙 _
  I_naturality _ := by simp
  S_naturality _ := by simp
  B_naturality _ := by simp

instance negId_isIso (X : ModuleCat ℚ) : IsIso (-𝟙 X) :=
  ⟨⟨-𝟙 X, by simp, by simp⟩⟩

/-- The comparison theorem, applied to the exact connective model. -/
theorem negHom_isIso_hcMap (n : ℕ) : IsIso ((negHom sbi).hcMap n) :=
  (negHom sbi).isIso_hcMap_of_isIso_hMap sbi_exact sbi_exact sbi_connective sbi_connective
    (fun m => negId_isIso (sbi.H m)) n

/-- The degree-bounded comparison only consults ordinary homology up to degree two. -/
theorem negHom_isIso_hcMap_two : IsIso ((negHom sbi).hcMap 2) :=
  (negHom sbi).isIso_hcMap_of_isIso_hMap_le sbi_exact sbi_exact sbi_connective sbi_connective 2
    (fun m _ => negId_isIso (sbi.H m))

/-- The two componentwise comparisons agree on the model. -/
theorem negHom_isIso_iff :
    (∀ n : ℕ, IsIso ((negHom sbi).hMap n)) ↔ ∀ n : ℕ, IsIso ((negHom sbi).hcMap n) :=
  (negHom sbi).isIso_hMap_iff_isIso_hcMap sbi_exact sbi_exact sbi_connective sbi_connective

/-- `evalHC` evaluates the morphism on an element where it is nonzero. -/
theorem evalHC_negHom_apply :
    ((NatSBIDiagram.evalHC 0).map (negHom sbi)).hom ((1 : ℚ), (2 : ℚ)) =
      ((-1 : ℚ), (-2 : ℚ)) := by
  change (-𝟙 V).hom ((1 : ℚ), (2 : ℚ)) = ((-1 : ℚ), (-2 : ℚ))
  simp

end MathlibExtTest.Algebra.Homology.MixedComplexSBIFocusedClients
