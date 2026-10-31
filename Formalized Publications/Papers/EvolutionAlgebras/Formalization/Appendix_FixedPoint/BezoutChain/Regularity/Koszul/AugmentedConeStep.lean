/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.ExteriorSumDecomposition
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.ChainCone

/-!
# The shared augmented cone step (A4(iii), file 4 of 6)

Over a general commutative ring `S`, augmented exactness of the Koszul chain
complex propagates across the cone step `K(φ') ⇝ K(φ)` given `×x` regularity
on homology — proved by matrix chase on the file-1 `extSplit` decomposition.
No `δ`/LES (deliberately bypassed per plan: the `δ`-as-`×x` identification is
absent from Mathlib).

* (§1) Linear-map-level exactness predicates `contractExactAt` /
  `contractAugExactZero`: the exact shape file 5 (`PolynomialExactness`: tower +
  var-regularity + induction) consumes — cycles/boundaries of `koszulContract`
  directly, no `sc'` unfolding.
* (§2) The cone matrices `koszulStep_matrix` / `koszulStep_bottom_matrix`,
  assembled from the file-3 bundled summand entries (`chainMatrix_*`).
* (§3) `koszulStep_exact_succ`: exactness at degrees `≥ 2` needs only the two
  adjacent exactness facts (no regularity, no augmentation).
* (§4) `koszulStep_exact_one`: exactness at degree 1 from `K'`-exactness at
  degree 1, augmented exactness at 0, and `×x`-regularity on `Q'`.
* (§5) The step augmentation `koszulStepAug = π ∘ ε' ∘ extSplitZero`: it kills
  boundaries, has every augmented cycle a boundary, and is surjective.
* (§6) Master `koszulStep_augmented_exact`: the one-step lemma in self-similar
  form (the conclusion matches the hypothesis shape at the next level, with
  `Q = Q' ⧸ x • Q'` presented by `π`).

Project (read-only): `Regularity/Koszul/ExteriorSumDecomposition.lean` (file 1 of 6: `extSplit`,
`extSplitZero`), `Regularity/Koszul/ChainCone.lean` (file 3 of 6: the
`chainMatrix_*` summand entries), `Regularity/Koszul/KoszulComplex.lean`
(`koszulContract`).

Consumers (sibling lanes): `PolynomialExactness` (file 5: instantiates `Q'`/`Q`
with the tower quotients `S ⧸ span rs`, `S ⧸ span (x :: rs)`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace AugmentedConeStep

open ExteriorAlgebra KoszulComplex ExteriorSumDecomposition ChainCone

variable {S : Type*} [CommRing S]
variable {M : Type*} [AddCommGroup M] [Module S M]
variable {Q' : Type*} [AddCommGroup Q'] [Module S Q']
variable {Q : Type*} [AddCommGroup Q] [Module S Q]

/-! ## §1. Linear-map-level exactness predicates -/

/-- Exactness of the Koszul contraction differential at degree `j + 1`: every
cycle is a boundary. Linear-map-level form of `HomologicalComplex.ExactAt`. -/
def contractExactAt {N : Type*} [AddCommGroup N] [Module S N]
    (ψ : N →ₗ[S] S) (j : ℕ) : Prop :=
  ∀ z : ↥(⋀[S]^(j + 1) N),
    koszulContract ψ j z = 0 →
      ∃ w : ↥(⋀[S]^((j + 1) + 1) N), koszulContract ψ (j + 1) w = z

/-- Augmented exactness at degree 0: the augmentation kills boundaries and
every augmented cycle is a boundary. -/
def contractAugExactZero {N : Type*} [AddCommGroup N] [Module S N]
    (ψ : N →ₗ[S] S) (ε : ↥(⋀[S]^0 N) →ₗ[S] Q') : Prop :=
  (∀ a : ↥(⋀[S]^1 N), ε (koszulContract ψ 0 a) = 0) ∧
    ∀ b : ↥(⋀[S]^0 N), ε b = 0 → ∃ c : ↥(⋀[S]^1 N), koszulContract ψ 0 c = b

/-! ## §2. Cone matrices from the file-3 summand entries -/

/-- The cone differential matrix from the file-3 summand entries: on `(a, b)`
the differential acts as `(d' a + x • b, -(d' b))`. -/
theorem koszulStep_matrix (i : ℕ) (φ : (M × S) →ₗ[S] S) (φ' : M →ₗ[S] S)
    (x : S) (phi_split : ∀ p : M × S, φ p = φ' p.1 + x * p.2)
    (a : ↥(⋀[S]^(i + 2) M)) (b : ↥(⋀[S]^(i + 1) M)) :
    extSplit i (koszulContract φ (i + 1) ((extSplit (i + 1)).symm (a, b))) =
      (koszulContract φ' (i + 1) a + x • b,
        -(koszulContract φ' i b)) := by
  have hsplit : (a, b) = (a, 0) + (0, b) := by ext <;> simp
  have h1 := chainMatrix_unshift i φ φ' x phi_split a
  have h2 := chainMatrix_shift i φ φ' x phi_split b
  rw [hsplit, map_add, map_add, map_add, h1, h2]
  ext <;> simp

/-- The bottom map from the file-3 entries: on `(a, b)` it acts as
`d' a + x • b` through `extSplitZero`. -/
theorem koszulStep_bottom_matrix (φ : (M × S) →ₗ[S] S) (φ' : M →ₗ[S] S)
    (x : S) (phi_split : ∀ p : M × S, φ p = φ' p.1 + x * p.2)
    (a : ↥(⋀[S]^1 M)) (b : ↥(⋀[S]^0 M)) :
    extSplitZero (koszulContract φ 0 ((extSplit 0).symm (a, b))) =
      koszulContract φ' 0 a + x • b := by
  have hsplit : (a, b) = (a, 0) + (0, b) := by ext <;> simp
  have h1 := chainMatrix_bottom_unshift φ φ' x phi_split a
  have h2 := chainMatrix_bottom_shift φ φ' x phi_split b
  rw [hsplit, map_add, map_add, map_add, h1, h2]

/-! ## §3. Exactness at degrees `≥ 2` (no regularity needed) -/

/-- Exactness propagates at degrees `≥ 2`: a `K`-cycle `(a, b)` gives a `K'`
cycle `b = d' c`, then `a + x • c = d' e`, and `(a, b) = d (e, -c)`. -/
theorem koszulStep_exact_succ (j : ℕ) (φ : (M × S) →ₗ[S] S)
    (φ' : M →ₗ[S] S) (x : S)
    (phi_split : ∀ p : M × S, φ p = φ' p.1 + x * p.2)
    (hexact : ∀ j, contractExactAt φ' j) :
    contractExactAt φ (j + 1) := by
  intro z hz
  generalize hp : extSplit (j + 1) z = p
  obtain ⟨a, b⟩ := p
  have hzsplit : (extSplit (j + 1)).symm (a, b) = z := by
    rw [← hp]
    exact (extSplit (j + 1)).symm_apply_apply z
  have hmat := koszulStep_matrix j φ φ' x phi_split a b
  rw [hzsplit, hz] at hmat
  simp only [map_zero] at hmat
  have hmat2 := hmat.symm
  have ha0 : koszulContract φ' (j + 1) a + x • b = 0 :=
    congrArg Prod.fst hmat2
  have h2 : -(koszulContract φ' j b) = 0 := congrArg Prod.snd hmat2
  have hb0 : koszulContract φ' j b = 0 := neg_eq_zero.mp h2
  obtain ⟨c, hc⟩ := hexact j b hb0
  have hmid : koszulContract φ' (j + 1) (a + x • c) = 0 := by
    rw [map_add, map_smul, hc]
    exact ha0
  obtain ⟨e, he⟩ := hexact (j + 1) (a + x • c) hmid
  refine ⟨(extSplit ((j + 1) + 1)).symm (e, -c), ?_⟩
  have hfin := koszulStep_matrix (j + 1) φ φ' x phi_split e (-c)
  rw [he] at hfin
  simp only [smul_neg, map_neg, neg_neg, hc] at hfin
  have habel : a + x • c + -(x • c) = a := by
    rw [← sub_eq_add_neg (a + x • c) (x • c)]
    exact add_sub_cancel_right _ _
  rw [habel] at hfin
  have hzw : extSplit (j + 1)
      (koszulContract φ ((j + 1) + 1)
        ((extSplit ((j + 1) + 1)).symm (e, -c))) =
      extSplit (j + 1) z := by
    rw [hfin, hp]
  have hinj : (extSplit (j + 1)).symm (extSplit (j + 1)
      (koszulContract φ ((j + 1) + 1)
        ((extSplit ((j + 1) + 1)).symm (e, -c)))) =
      (extSplit (j + 1)).symm (extSplit (j + 1) z) := by
    rw [hzw]
  simp only [LinearEquiv.symm_apply_apply] at hinj
  exact hinj

/-! ## §4. Exactness at degree 1 (`×x`-regularity enters) -/

/-- Exactness at degree 1: from `d' a + x • b = 0` the augmentation gives
`x • ε' b = 0`, regularity gives `ε' b = 0`, hence `b = d' c`, and the chase
closes as in §3. -/
theorem koszulStep_exact_one (φ : (M × S) →ₗ[S] S) (φ' : M →ₗ[S] S)
    (x : S) (phi_split : ∀ p : M × S, φ p = φ' p.1 + x * p.2)
    (ε' : ↥(⋀[S]^0 M) →ₗ[S] Q')
    (hexact0 : contractExactAt φ' 0)
    (haug : contractAugExactZero φ' ε')
    (hreg : ∀ q : Q', x • q = 0 → q = 0) :
    contractExactAt φ 0 := by
  intro z hz
  generalize hp : extSplit 0 z = p
  obtain ⟨a, b⟩ := p
  have hzsplit : (extSplit 0).symm (a, b) = z := by
    rw [← hp]
    exact (extSplit 0).symm_apply_apply z
  have hmat := koszulStep_bottom_matrix φ φ' x phi_split a b
  rw [hzsplit, hz] at hmat
  simp only [map_zero] at hmat
  have ha0 : koszulContract φ' 0 a + x • b = 0 := hmat.symm
  have hxreg : x • ε' b = 0 := by
    have h := congrArg ε' ha0
    rw [map_add, map_smul, haug.1 a, zero_add, map_zero] at h
    exact h
  have hb0 : ε' b = 0 := hreg _ hxreg
  obtain ⟨c, hc⟩ := haug.2 b hb0
  have hmid : koszulContract φ' 0 (a + x • c) = 0 := by
    rw [map_add, map_smul, hc]
    exact ha0
  obtain ⟨e, he⟩ := hexact0 (a + x • c) hmid
  refine ⟨(extSplit (0 + 1)).symm (e, -c), ?_⟩
  have hfin := koszulStep_matrix 0 φ φ' x phi_split e (-c)
  rw [he] at hfin
  simp only [smul_neg, map_neg, neg_neg, hc] at hfin
  have habel : a + x • c + -(x • c) = a := by
    rw [← sub_eq_add_neg (a + x • c) (x • c)]
    exact add_sub_cancel_right _ _
  rw [habel] at hfin
  have hzw : extSplit 0
      (koszulContract φ (0 + 1) ((extSplit (0 + 1)).symm (e, -c))) =
      extSplit 0 z := by
    rw [hfin, hp]
  have hinj : (extSplit 0).symm (extSplit 0
      (koszulContract φ (0 + 1) ((extSplit (0 + 1)).symm (e, -c)))) =
      (extSplit 0).symm (extSplit 0 z) := by
    rw [hzw]
  simp only [LinearEquiv.symm_apply_apply] at hinj
  exact hinj

/-! ## §5. The step augmentation -/

/-- The step augmentation `π ∘ ε' ∘ extSplitZero`: degree-0 classes of `K`
map through the degree-0 split and the quotient presentation `π`. -/
noncomputable def koszulStepAug (ε' : ↥(⋀[S]^0 M) →ₗ[S] Q')
    (π : Q' →ₗ[S] Q) : ↥(⋀[S]^0 (M × S)) →ₗ[S] Q :=
  π.comp (ε'.comp extSplitZero.toLinearMap)

/-- The step augmentation computes through the degree-0 split. -/
@[simp]
theorem koszulStepAug_apply (ε' : ↥(⋀[S]^0 M) →ₗ[S] Q')
    (π : Q' →ₗ[S] Q) (z : ↥(⋀[S]^0 (M × S))) :
    koszulStepAug ε' π z = π (ε' (extSplitZero z)) :=
  rfl

/-- The step augmentation kills `K`-boundaries: on `(a', b')` the bottom map
gives `d' a' + x • b'`, and `π` kills both the boundary (`ε'` does) and the
`x`-multiple (`hxQ` does). -/
theorem koszulStep_augZero_maps (φ : (M × S) →ₗ[S] S) (φ' : M →ₗ[S] S)
    (x : S) (phi_split : ∀ p : M × S, φ p = φ' p.1 + x * p.2)
    (ε' : ↥(⋀[S]^0 M) →ₗ[S] Q') (π : Q' →ₗ[S] Q)
    (haug : contractAugExactZero φ' ε')
    (hxQ : ∀ q : Q', π (x • q) = 0) :
    ∀ a : ↥(⋀[S]^1 (M × S)),
      koszulStepAug ε' π (koszulContract φ 0 a) = 0 := by
  intro a
  generalize hp : extSplit 0 a = p
  obtain ⟨a', b'⟩ := p
  have hasplit : (extSplit 0).symm (a', b') = a := by
    rw [← hp]
    exact (extSplit 0).symm_apply_apply a
  have hmat := koszulStep_bottom_matrix φ φ' x phi_split a' b'
  rw [hasplit] at hmat
  rw [koszulStepAug_apply, hmat, map_add, map_smul, haug.1 a', zero_add]
  exact hxQ _

/-- Every augmented `K`-cycle is a boundary: `π (ε' c) = 0` presents
`ε' c = x • t`, lifting `t` through `ε'` leaves an augmented `K'`-cycle
`d' e'`, and `(e', b̃)` hits `c` through the bottom map. -/
theorem koszulStep_augZero_exact (φ : (M × S) →ₗ[S] S) (φ' : M →ₗ[S] S)
    (x : S) (phi_split : ∀ p : M × S, φ p = φ' p.1 + x * p.2)
    (ε' : ↥(⋀[S]^0 M) →ₗ[S] Q') (π : Q' →ₗ[S] Q)
    (haug : contractAugExactZero φ' ε')
    (hsurj : Function.Surjective ε')
    (hkerπ : ∀ q : Q', π q = 0 → ∃ t : Q', x • t = q) :
    ∀ c : ↥(⋀[S]^0 (M × S)),
      koszulStepAug ε' π c = 0 →
        ∃ w : ↥(⋀[S]^1 (M × S)), koszulContract φ 0 w = c := by
  intro c hc
  rw [koszulStepAug_apply] at hc
  obtain ⟨t, ht⟩ := hkerπ _ hc
  obtain ⟨btil, hbtil⟩ := hsurj t
  have hmem : ε' (extSplitZero c - x • btil) = 0 := by
    rw [map_sub, map_smul, hbtil, ht, sub_self]
  obtain ⟨e', he'⟩ := haug.2 _ hmem
  have hdecomp : extSplitZero c = koszulContract φ' 0 e' + x • btil := by
    rw [he']
    exact (sub_add_cancel _ _).symm
  refine ⟨(extSplit 0).symm (e', btil), ?_⟩
  have hmat := koszulStep_bottom_matrix φ φ' x phi_split e' btil
  have hzw : extSplitZero
      (koszulContract φ 0 ((extSplit 0).symm (e', btil))) =
      extSplitZero c :=
    hmat.trans hdecomp.symm
  have hinj : extSplitZero.symm (extSplitZero
      (koszulContract φ 0 ((extSplit 0).symm (e', btil)))) =
      extSplitZero.symm (extSplitZero c) := by
    rw [hzw]
  simp only [LinearEquiv.symm_apply_apply] at hinj
  exact hinj

/-- The step augmentation is surjective. -/
theorem koszulStep_aug_surjective (ε' : ↥(⋀[S]^0 M) →ₗ[S] Q')
    (π : Q' →ₗ[S] Q) (hsurj : Function.Surjective ε')
    (hsurjπ : Function.Surjective π) :
    Function.Surjective (koszulStepAug ε' π) := by
  intro q
  obtain ⟨q', hq'⟩ := hsurjπ q
  obtain ⟨b, hb⟩ := hsurj q'
  refine ⟨extSplitZero.symm b, ?_⟩
  rw [koszulStepAug_apply, LinearEquiv.apply_symm_apply, hb, hq']

/-! ## §6. The master one-step lemma -/

/-- Master augmented cone step: `K'`-exactness at all positive degrees plus
augmented exactness at 0, `×x`-regularity on `Q'`, and the quotient
presentation `π` of `Q = Q' ⧸ x • Q'` give the same package for `K`. The
conclusion matches the hypothesis shape at the next level, so file 5's tower
induction applies this directly. -/
theorem koszulStep_augmented_exact (φ : (M × S) →ₗ[S] S) (φ' : M →ₗ[S] S)
    (x : S) (phi_split : ∀ p : M × S, φ p = φ' p.1 + x * p.2)
    (ε' : ↥(⋀[S]^0 M) →ₗ[S] Q') (π : Q' →ₗ[S] Q)
    (hexact : ∀ j, contractExactAt φ' j)
    (haug : contractAugExactZero φ' ε')
    (hsurj : Function.Surjective ε')
    (hreg : ∀ q : Q', x • q = 0 → q = 0)
    (hxQ : ∀ q : Q', π (x • q) = 0)
    (hkerπ : ∀ q : Q', π q = 0 → ∃ t : Q', x • t = q)
    (hsurjπ : Function.Surjective π) :
    (∀ j, contractExactAt φ j) ∧
      contractAugExactZero φ (koszulStepAug ε' π) ∧
        Function.Surjective (koszulStepAug ε' π) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    cases j with
    | zero =>
        exact koszulStep_exact_one φ φ' x phi_split ε' (hexact 0) haug hreg
    | succ j =>
        exact koszulStep_exact_succ j φ φ' x phi_split hexact
  · exact ⟨koszulStep_augZero_maps φ φ' x phi_split ε' π haug hxQ,
      koszulStep_augZero_exact φ φ' x phi_split ε' π haug hsurj hkerπ⟩
  · exact koszulStep_aug_surjective ε' π hsurj hsurjπ

end AugmentedConeStep
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
