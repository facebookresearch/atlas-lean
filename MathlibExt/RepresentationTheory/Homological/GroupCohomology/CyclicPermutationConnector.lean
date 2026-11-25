/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneAny
public import MathlibExt.RepresentationTheory.Rep.CyclicPermutation
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-!
# The cyclic permutation connector as cup with the quotient character

For mod-two coefficients, lift an `A`-valued cochain into the cyclic
permutation coefficient by placing its value at cyclic index zero and zero
at index one.  This lift augments back to the original cochain.  Its
differential differs from the lifted cocycle equation only in the first
face: translation of the cyclic index by the quotient character.  The
resulting diagonal defect is

`chi(g₀) • g₀ · z(g₁, ..., gₙ)`,

which is the inhomogeneous `(1,n)` cup formula.  The concrete connecting
morphism formula therefore identifies the cyclic connector with cup by the
character class in every degree.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory MonoidalCategory

namespace groupCohomology

variable {G : Type} [Group G]

/-- Degree transport on inhomogeneous cochains is precomposition with the
corresponding cast of finite tuple indices. -/
theorem inhomogeneousCochains_XIsoOfEq_hom_apply
    (A : Rep.{0} (ZMod 2) G) {p q : ℕ} (h : p = q)
    (f : (Fin p → G) → A) (g : Fin q → G) :
    (((inhomogeneousCochains A).XIsoOfEq h).hom.hom f) g =
      f (fun i => g (Fin.cast h i)) := by
  subst q
  rfl

/-- The additive mod-two value of a multiplicative cyclic character. -/
def cyclicCharacterValue
    (chi : G →* Multiplicative (ZMod 2)) (g : G) : ZMod 2 :=
  Multiplicative.toAdd (chi g)

@[simp]
theorem cyclicCharacterValue_mul
    (chi : G →* Multiplicative (ZMod 2)) (g h : G) :
    cyclicCharacterValue chi (g * h) =
      cyclicCharacterValue chi g + cyclicCharacterValue chi h := by
  unfold cyclicCharacterValue
  rw [map_mul]
  rfl

/-- Low-degree cocycle representing the cyclic character. -/
def cyclicCharacterCocycleOne
    (chi : G →* Multiplicative (ZMod 2)) :
    cocycles₁ (Rep.trivial (ZMod 2) G (ZMod 2)) :=
  ⟨fun g => cyclicCharacterValue chi g,
    (mem_cocycles₁_iff _).2 (fun g h => by
      rw [cyclicCharacterValue_mul]
      change cyclicCharacterValue chi g + cyclicCharacterValue chi h =
        cyclicCharacterValue chi h + cyclicCharacterValue chi g
      exact add_comm _ _)⟩

/-- Degree-one arbitrary-complex cocycle representing the cyclic
character. -/
noncomputable def cyclicCharacterCocycle
    (chi : G →* Multiplicative (ZMod 2)) :
    cocycles (Rep.trivial (ZMod 2) G (ZMod 2)) 1 :=
  (isoCocycles₁ _).inv (cyclicCharacterCocycleOne chi)

@[simp]
theorem cyclicCharacterCocycle_apply
    (chi : G →* Multiplicative (ZMod 2)) (q : Fin 1 → G) :
    (iCocycles (Rep.trivial (ZMod 2) G (ZMod 2)) 1).hom
        (cyclicCharacterCocycle chi) q =
      cyclicCharacterValue chi (q 0) := by
  unfold cyclicCharacterCocycle
  rw [← cocyclesMk₁_eq, iCocycles_mk]
  rfl

/-- Character evaluation in the tensor-unit coefficient presentation. -/
theorem cyclicCharacterCocycle_tensorUnit_apply
    (chi : G →* Multiplicative (ZMod 2)) (q : Fin 1 → G) :
    (iCocycles (𝟙_ (Rep.{0} (ZMod 2) G)) 1).hom
        (cyclicCharacterCocycle chi) q =
      cyclicCharacterValue chi (q 0) :=
  cyclicCharacterCocycle_apply chi q

/-- The group-cohomology class of the mod-two cyclic character. -/
noncomputable def cyclicCharacterClass
    (chi : G →* Multiplicative (ZMod 2)) :
    groupCohomology (Rep.trivial (ZMod 2) G (ZMod 2)) 1 :=
  π _ 1 (cyclicCharacterCocycle chi)

/-- Low-degree presentation of the cyclic-character cohomology class. -/
theorem cyclicCharacterClass_eq_H1π
    (chi : G →* Multiplicative (ZMod 2)) :
    cyclicCharacterClass chi =
      H1π (Rep.trivial (ZMod 2) G (ZMod 2))
        (cyclicCharacterCocycleOne chi) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The cyclic-character class is natural under pullback of the group. -/
theorem cyclicCharacterClass_naturality
    {J : Type} [Group J] (f : J →* G)
    (chi : G →* Multiplicative (ZMod 2)) :
    groupCohomology.map f (𝟙 _) 1 (cyclicCharacterClass chi) =
      cyclicCharacterClass (chi.comp f) := by
  let T := Rep.trivial (ZMod 2) G (ZMod 2)
  let TJ := Rep.trivial (ZMod 2) J (ZMod 2)
  let phi : Rep.res f T ⟶ TJ := 𝟙 _
  have hCycles :
      HomologicalComplex.cyclesMap (cochainsMap f phi) 1
          (cyclicCharacterCocycle chi) =
        cyclicCharacterCocycle (chi.comp f) := by
    apply (ModuleCat.mono_iff_injective (iCocycles TJ 1)).mp inferInstance
    have hm := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (cochainsMap f phi) 1)
      (cyclicCharacterCocycle chi)
    simp only [ConcreteCategory.comp_apply] at hm
    rw [hm]
    funext q
    change phi.hom
        ((iCocycles T 1).hom (cyclicCharacterCocycle chi)
          (fun i => f (q i))) =
      (iCocycles TJ 1).hom
        (cyclicCharacterCocycle (chi.comp f)) q
    rw [cyclicCharacterCocycle_apply, cyclicCharacterCocycle_apply]
    rfl
  have hπ := ConcreteCategory.congr_hom
    (groupCohomology.π_map f phi 1)
    (cyclicCharacterCocycle chi)
  simp only [ConcreteCategory.comp_apply] at hπ
  change groupCohomology.map f phi 1
      ((π T 1).hom (cyclicCharacterCocycle chi)) = _
  unfold cyclicCharacterClass
  rw [hπ, hCycles]

/-- The zero-index linear section of cyclic augmentation. -/
def cyclicPermutationZeroSection
    (A : Rep.{0} (ZMod 2) G) (a : A) : ZMod 2 → A :=
  fun i => if i = 0 then a else 0

@[simp]
theorem cyclicPermutationZeroSection_zero
    (A : Rep.{0} (ZMod 2) G) (a : A) :
    cyclicPermutationZeroSection A a 0 = a := by
  simp [cyclicPermutationZeroSection]

@[simp]
theorem cyclicPermutationZeroSection_one
    (A : Rep.{0} (ZMod 2) G) (a : A) :
    cyclicPermutationZeroSection A a 1 = 0 := by
  simp [cyclicPermutationZeroSection]

/-- The zero-index section is a right inverse to cyclic augmentation. -/
theorem cyclicPermutationAugmentation_zeroSection
    (chi : G →* Multiplicative (ZMod 2))
    (A : Rep.{0} (ZMod 2) G) (a : A) :
    (Rep.cyclicPermutationAugmentation 2 chi A).hom
        (cyclicPermutationZeroSection A a) = a := by
  rw [Rep.cyclicPermutationAugmentation_apply, Rep.sum_zmodTwo]
  simp

/-- Cochain obtained by applying the zero-index section pointwise. -/
def cyclicPermutationZeroSectionCochain
    (chi : G →* Multiplicative (ZMod 2))
    (A : Rep.{0} (ZMod 2) G) (n : ℕ)
    (z : (Fin n → G) → A) :
    (Fin n → G) → Rep.cyclicPermutation 2 chi A :=
  fun q => cyclicPermutationZeroSection A (z q)

/-- The explicit character-cup cochain in target-normalized degree. -/
def cyclicCharacterCupCochain
    (chi : G →* Multiplicative (ZMod 2))
    (A : Rep.{0} (ZMod 2) G) (n : ℕ)
    (z : (Fin n → G) → A) :
    (Fin (n + 1) → G) → A :=
  fun g => cyclicCharacterValue chi (g 0) •
    A.ρ (g 0) (z (fun i => g i.succ))

private theorem neg_eq_self_zmodTwo_module
    (A : Rep.{0} (ZMod 2) G) (a : A) : -a = a := by
  calc
    -a = (-1 : ZMod 2) • a := (neg_one_smul (ZMod 2) a).symm
    _ = (1 : ZMod 2) • a := by rw [show (-1 : ZMod 2) = 1 by decide]
    _ = a := one_smul (ZMod 2) a

-- The arbitrary-degree differential expands a finite alternating sum.
/-- The differential of the zero-index lift of a cocycle is the diagonal
of the character-cup cochain. -/
theorem cyclicPermutationZeroSectionCochain_d
    (chi : G →* Multiplicative (ZMod 2))
    (A : Rep.{0} (ZMod 2) G) (n : ℕ)
    (z : (Fin n → G) → A)
    (hz : (inhomogeneousCochains.d A n).hom z = 0) :
    (inhomogeneousCochains.d
        (Rep.cyclicPermutation 2 chi A) n).hom
        (fun q => cyclicPermutationZeroSection A (z q)) =
      fun g => (Rep.cyclicPermutationDiagonal 2 chi A).hom
        (cyclicCharacterCupCochain chi A n z g) := by
  funext g
  funext i
  have hzG :
      A.ρ (g 0) (z fun i => g i.succ) +
          ∑ j : Fin (n + 1),
            (-1 : ZMod 2) ^ ((j : ℕ) + 1) •
              z (Fin.contractNth j (fun x y : G => x * y) g) = 0 := by
    have h := congrFun hz g
    change A.ρ (g 0) (z fun i => g i.succ) +
        ∑ j : Fin (n + 1),
          (-1 : ZMod 2) ^ ((j : ℕ) + 1) •
            z (Fin.contractNth j (fun x y : G => x * y) g) =
      (0 : A) at h
    exact h
  simp only [inhomogeneousCochains.d_hom_apply]
  change A.ρ (g 0)
        (cyclicPermutationZeroSection A (z fun i => g i.succ)
          (i + Multiplicative.toAdd (chi (g 0)))) +
      (∑ j : Fin (n + 1),
        (-1 : ZMod 2) ^ ((j : ℕ) + 1) •
          cyclicPermutationZeroSection A
            (z (Fin.contractNth j (fun x y : G => x * y) g))) i =
    cyclicCharacterCupCochain chi A n z g
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply]
  unfold cyclicCharacterCupCochain cyclicCharacterValue
  rcases Rep.zmodTwo_eq_zero_or_one
      (cyclicCharacterValue chi (g 0)) with hc | hc <;>
    rcases Rep.zmodTwo_eq_zero_or_one i with hi | hi
  all_goals
    change Multiplicative.toAdd (chi (g 0)) = _ at hc
  · rw [hc, hi]
    simp only [zero_smul, zero_add, cyclicPermutationZeroSection_zero]
    exact hzG
  · rw [hc, hi]
    simp [cyclicPermutationZeroSection]
  · rw [hc, hi]
    simp only [one_smul, zero_add, cyclicPermutationZeroSection_one,
      map_zero]
    have hsum :
        ∑ j : Fin (n + 1),
            (-1 : ZMod 2) ^ ((j : ℕ) + 1) •
              z (Fin.contractNth j (fun x y : G => x * y) g) =
          -(A.ρ (g 0) (z fun i => g i.succ)) :=
      eq_neg_of_add_eq_zero_right hzG
    simp_rw [cyclicPermutationZeroSection_zero]
    rw [hsum, neg_eq_self_zmodTwo_module]
  · rw [hc, hi]
    simp [cyclicPermutationZeroSection,
      show (1 : ZMod 2) + 1 = 0 by decide]

set_option backward.isDefEq.respectTransparency false in
/-- The explicit character-cup cochain is a cocycle whenever its right
input is a cocycle. -/
theorem cyclicCharacterCupCochain_cocycle
    (chi : G →* Multiplicative (ZMod 2))
    (A : Rep.{0} (ZMod 2) G) (n : ℕ)
    (z : (Fin n → G) → A)
    (hz : (inhomogeneousCochains.d A n).hom z = 0) :
    (inhomogeneousCochains.d A (n + 1)).hom
        (cyclicCharacterCupCochain chi A n z) = 0 := by
  let P := Rep.cyclicPermutation 2 chi A
  let _ : Mono (Rep.cyclicPermutationDiagonal 2 chi A) :=
    (Rep.mono_iff_injective _).2
      (Rep.cyclicPermutationDiagonal_two_injective chi A)
  let D := cochainsMap (MonoidHom.id G)
    (Rep.cyclicPermutationDiagonal 2 chi A)
  let y : (Fin n → G) → P :=
    fun q => cyclicPermutationZeroSection A (z q)
  let x := cyclicCharacterCupCochain chi A n z
  have hBoundary :
      (inhomogeneousCochains.d P n).hom y =
        fun g => (Rep.cyclicPermutationDiagonal 2 chi A).hom (x g) :=
    cyclicPermutationZeroSectionCochain_d chi A n z hz
  apply (ModuleCat.mono_iff_injective (D.f (n + 2))).mp inferInstance
  rw [map_zero]
  change (D.f (n + 2)).hom
    ((inhomogeneousCochains.d A (n + 1)).hom x) = 0
  have hComm := ConcreteCategory.congr_hom
    (D.comm (n + 1) (n + 2)) x
  simp only [ConcreteCategory.comp_apply] at hComm
  have hdA := ConcreteCategory.congr_hom
    (inhomogeneousCochains.d_def A (n + 1)) x
  have hdP := ConcreteCategory.congr_hom
    (inhomogeneousCochains.d_def P (n + 1)) ((D.f (n + 1)).hom x)
  have hComm' :
      (inhomogeneousCochains.d P (n + 1)).hom
          ((D.f (n + 1)).hom x) =
        (D.f (n + 2)).hom
          ((inhomogeneousCochains.d A (n + 1)).hom x) := by
    calc
      (inhomogeneousCochains.d P (n + 1)).hom
          ((D.f (n + 1)).hom x) =
        ((inhomogeneousCochains P).d (n + 1) (n + 2)).hom
          ((D.f (n + 1)).hom x) := hdP.symm
      _ = (D.f (n + 2)).hom
          (((inhomogeneousCochains A).d (n + 1) (n + 2)).hom x) := hComm
      _ = (D.f (n + 2)).hom
          ((inhomogeneousCochains.d A (n + 1)).hom x) :=
        congrArg (D.f (n + 2)).hom hdA
  rw [← hComm']
  change (inhomogeneousCochains.d P (n + 1)).hom
      ((D.f (n + 1)).hom x) = 0
  have hDx : (D.f (n + 1)).hom x =
      (inhomogeneousCochains.d P n).hom y := by
    exact hBoundary.symm
  rw [hDx]
  have hdd := congrArg
    (fun f => f.hom y)
    (inhomogeneousCochains.d_comp_d (A := P) n)
  change (inhomogeneousCochains.d P (n + 1)).hom
      ((inhomogeneousCochains.d P n).hom y) = 0 at hdd
  exact hdd

/-- The explicit arbitrary-degree character-cup cocycle. -/
noncomputable def cyclicCharacterCupCocycle
    (chi : G →* Multiplicative (ZMod 2))
    (A : Rep.{0} (ZMod 2) G) (n : ℕ)
    (z : cocycles A n) : cocycles A (n + 1) :=
  cocyclesMk
    (cyclicCharacterCupCochain chi A n ((iCocycles A n).hom z))
    (cyclicCharacterCupCochain_cocycle chi A n
      ((iCocycles A n).hom z) (by
        have h := ConcreteCategory.congr_hom
          ((inhomogeneousCochains A).iCycles_d n (n + 1)) z
        rw [inhomogeneousCochains.d_def] at h
        simpa only [ConcreteCategory.comp_apply, ModuleCat.hom_zero,
          LinearMap.zero_apply] using h))

@[simp]
theorem cyclicCharacterCupCocycle_apply
    (chi : G →* Multiplicative (ZMod 2))
    (A : Rep.{0} (ZMod 2) G) (n : ℕ)
    (z : cocycles A n) (g : Fin (n + 1) → G) :
    (iCocycles A (n + 1)).hom
        (cyclicCharacterCupCocycle chi A n z) g =
      cyclicCharacterCupCochain chi A n
        ((iCocycles A n).hom z) g := by
  unfold cyclicCharacterCupCocycle
  rw [iCocycles_mk]

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary cyclic-permutation connector sends a cocycle class to the
explicit character-cup cocycle class. -/
theorem cyclicPermutationTwo_delta_π
    (chi : G →* Multiplicative (ZMod 2))
    (A : Rep.{0} (ZMod 2) G) (n : ℕ)
    (z : cocycles A n) :
    (δ (Rep.cyclicPermutationTwoShortComplex_shortExact chi A)
        n (n + 1) rfl).hom (π A n z) =
      π A (n + 1) (cyclicCharacterCupCocycle chi A n z) := by
  let P := Rep.cyclicPermutation 2 chi A
  let S := Rep.cyclicPermutationTwoShortComplex chi A
  let hS := Rep.cyclicPermutationTwoShortComplex_shortExact chi A
  let zf := (iCocycles A n).hom z
  have hz : (inhomogeneousCochains.d A n).hom zf = 0 := by
    have h := ConcreteCategory.congr_hom
      ((inhomogeneousCochains A).iCycles_d n (n + 1)) z
    rw [inhomogeneousCochains.d_def] at h
    simpa only [ConcreteCategory.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h
  let y : (Fin n → G) → P :=
    fun q => cyclicPermutationZeroSection A (zf q)
  have hy :
      ((cochainsMap (MonoidHom.id G) S.g).f n).hom y = zf := by
    funext q
    change (Rep.cyclicPermutationAugmentation 2 chi A).hom
      (cyclicPermutationZeroSection A (zf q)) = zf q
    exact cyclicPermutationAugmentation_zeroSection chi A (zf q)
  let x := cyclicCharacterCupCochain chi A n zf
  have hx : S.f.hom ∘ x =
      (inhomogeneousCochains.d P n).hom y := by
    have h := cyclicPermutationZeroSectionCochain_d chi A n zf hz
    change (fun g => (Rep.cyclicPermutationDiagonal 2 chi A).hom
      (x g)) = _
    exact h.symm
  have hzS :
      ((inhomogeneousCochains S.X₃).d n (n + 1)).hom zf = 0 := by
    rw [inhomogeneousCochains.d_def]
    exact hz
  have hxS : S.f.hom ∘ x =
      ((inhomogeneousCochains S.X₂).d n (n + 1)).hom y := by
    rw [inhomogeneousCochains.d_def]
    exact hx
  have hδ := δ_apply hS rfl zf hzS y hy x hxS
  change (δ hS n (n + 1) rfl).hom
      ((π A n).hom (cocyclesMk zf _)) =
    (π A (n + 1)).hom (cocyclesMkOfCompEqD hS hxS) at hδ
  have hzEq (h0 : (inhomogeneousCochains.d A n).hom zf = 0) :
      cocyclesMk zf h0 = z := by
    apply (ModuleCat.mono_iff_injective (iCocycles A n)).mp inferInstance
    rw [iCocycles_mk]
  have hxEq : cocyclesMkOfCompEqD hS hxS =
      cyclicCharacterCupCocycle chi A n z := by
    apply (ModuleCat.mono_iff_injective (iCocycles A (n + 1))).mp
      inferInstance
    rw [iCocycles_mk]
    funext g
    exact (cyclicCharacterCupCocycle_apply chi A n z g).symm
  rw [hzEq, hxEq] at hδ
  exact hδ

/-- Character cup constructed through the arbitrary cup product and the
left coefficient unitor. -/
noncomputable def cyclicCharacterCupCocycleViaCup
    (chi : G →* Multiplicative (ZMod 2))
    (A : Rep.{0} (ZMod 2) G) (n : ℕ)
    (z : cocycles A n) : cocycles A (n + 1) :=
  HomologicalComplex.cyclesMap
    (cochainsMap (MonoidHom.id G) (λ_ A).hom) (n + 1)
    (((inhomogeneousCochains
      (Rep.trivial (ZMod 2) G (ZMod 2) ⊗ A)).cyclesIsoOfEq
        (Nat.one_add n)).hom.hom
      (((inhomogeneousCupPairing G (ZMod 2)
        (Rep.trivial (ZMod 2) G (ZMod 2)) A).pairCycles 1 n).hom
        (cyclicCharacterCocycle chi ⊗ₜ[ZMod 2] z)))

-- Degree transport and the explicit Alexander--Whitney formula are expanded.
set_option backward.isDefEq.respectTransparency false in
/-- The abstract arbitrary cup cocycle is the explicit character-cup
cocycle used in the connector computation. -/
theorem cyclicCharacterCupCocycleViaCup_eq
    (chi : G →* Multiplicative (ZMod 2))
    (A : Rep.{0} (ZMod 2) G) (n : ℕ)
    (z : cocycles A n) :
    cyclicCharacterCupCocycleViaCup chi A n z =
      cyclicCharacterCupCocycle chi A n z := by
  let T : Rep.{0} (ZMod 2) G := 𝟙_ (Rep.{0} (ZMod 2) G)
  let p : cocycles (T ⊗ A) (1 + n) :=
    ((inhomogeneousCupPairing G (ZMod 2) T A).pairCycles 1 n).hom
      (cyclicCharacterCocycle chi ⊗ₜ[ZMod 2] z)
  let t : cocycles (T ⊗ A) (n + 1) :=
    (((inhomogeneousCochains (T ⊗ A)).cyclesIsoOfEq
      (Nat.one_add n)).hom.hom p)
  apply (ModuleCat.mono_iff_injective (iCocycles A (n + 1))).mp
    inferInstance
  have hMap := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i
      (cochainsMap (MonoidHom.id G) (λ_ A).hom) (n + 1)) t
  have hTransport := ConcreteCategory.congr_hom
    ((inhomogeneousCochains (T ⊗ A)).cyclesIsoOfEq_hom_iCycles
      (Nat.one_add n)) p
  simp only [ConcreteCategory.comp_apply] at hMap hTransport
  change (iCocycles A (n + 1)).hom
      (HomologicalComplex.cyclesMap
        (cochainsMap (MonoidHom.id G) (λ_ A).hom) (n + 1) t) =
    (iCocycles A (n + 1)).hom
      (cyclicCharacterCupCocycle chi A n z)
  rw [hMap]
  calc
    ((cochainsMap (MonoidHom.id G) (λ_ A).hom).f (n + 1)).hom
        ((iCocycles (T ⊗ A) (n + 1)).hom t) =
      ((cochainsMap (MonoidHom.id G) (λ_ A).hom).f (n + 1)).hom
        (((inhomogeneousCochains (T ⊗ A)).XIsoOfEq
          (Nat.one_add n)).hom.hom
          ((iCocycles (T ⊗ A) (1 + n)).hom p)) :=
        congrArg
          ((cochainsMap (MonoidHom.id G) (λ_ A).hom).f (n + 1)).hom
          hTransport
    _ = (iCocycles A (n + 1)).hom
        (cyclicCharacterCupCocycle chi A n z) := by
      funext g
      change (λ_ A).hom.hom
          ((((inhomogeneousCochains (T ⊗ A)).XIsoOfEq
            (Nat.one_add n)).hom.hom
            ((iCocycles (T ⊗ A) (1 + n)).hom p)) g) = _
      rw [inhomogeneousCochains_XIsoOfEq_hom_apply]
      dsimp only [p, T]
      rw [HomologicalComplex.CochainGradedPairing.pairCycles_i_apply]
      rw [inhomogeneousCupPairing_apply]
      rw [cyclicCharacterCupCocycle_apply]
      unfold cyclicCharacterCupCochain
      rw [cyclicCharacterCocycle_tensorUnit_apply]
      let g' : Fin (1 + n) → G :=
        fun i => g (Fin.cast (Nat.one_add n) i)
      change (λ_ A).hom.hom
          (cyclicCharacterValue chi (g' (Fin.castAdd n (0 : Fin 1))) ⊗ₜ[ZMod 2]
            A.ρ (Fin.partialProd g' (Fin.natAdd 1 (0 : Fin (n + 1))))
              ((iCocycles A n).hom z
                (fun i => g' (Fin.natAdd 1 i)))) = _
      rw [Rep.hom_hom_leftUnitor]
      change cyclicCharacterValue chi (g' (Fin.castAdd n (0 : Fin 1))) •
          A.ρ (Fin.partialProd g' (Fin.natAdd 1 (0 : Fin (n + 1))))
            ((iCocycles A n).hom z
              (fun i => g' (Fin.natAdd 1 i))) = _
      apply congrArg₂ (fun (r : ZMod 2) (a : A) => r • a)
      · apply congrArg (cyclicCharacterValue chi)
        dsimp only [g']
        apply congrArg g
        apply Fin.ext
        simp
      · apply congrArg₂ (fun (h : G) (a : A) => A.ρ h a)
        · have hidx :
              Fin.natAdd 1 (0 : Fin (n + 1)) =
                (0 : Fin (1 + n)).succ := by
            apply Fin.ext
            simp only [Fin.val_natAdd, Fin.val_succ, Fin.val_zero,
              Nat.add_zero]
          rw [hidx, Fin.partialProd_succ]
          have hzero :
              Fin.castSucc (0 : Fin (1 + n)) =
                (0 : Fin ((1 + n) + 1)) := by
            apply Fin.ext
            rfl
          rw [hzero, Fin.partialProd_zero, one_mul]
          dsimp only [g']
          apply congrArg g
          apply Fin.ext
          simp
        · apply congrArg ((iCocycles A n).hom z)
          funext i
          dsimp only [g']
          apply congrArg g
          apply Fin.ext
          simp

/-- Linear map given by cup product with the cyclic character on the left,
followed by the coefficient left unitor. -/
noncomputable def cyclicCharacterCupMap
    (chi : G →* Multiplicative (ZMod 2))
    (A : Rep.{0} (ZMod 2) G) (n : ℕ) :
    groupCohomology A n ⟶ groupCohomology A (n + 1) :=
  cupOneClassMap (cyclicCharacterClass chi) (λ_ A).hom n

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- After mapping the cyclic-character coefficient through `phi`, the
character cup transported to `B ⊗ A` is cup by the mapped character class. -/
theorem cyclicCharacterCupMap_comp_leftTensorInsertion
    (chi : G →* Multiplicative (ZMod 2))
    (A B : Rep.{0} (ZMod 2) G)
    (phi : Rep.trivial (ZMod 2) G (ZMod 2) ⟶ B)
    (n : ℕ) :
    cyclicCharacterCupMap chi A n ≫
        map (MonoidHom.id G)
          ((λ_ A).inv ≫ (phi ⊗ₘ 𝟙 A)) (n + 1) =
      cupOneClassMap
        ((map (MonoidHom.id G) phi 1).hom
          (cyclicCharacterClass chi))
        (𝟙 (B ⊗ A)) n :=
  cupOneClassMap_leftUnitor_naturality
    (cyclicCharacterClass chi) phi n

set_option backward.isDefEq.respectTransparency false in
/-- Cup with the character sends a represented cocycle to the explicit
character-cup cocycle class. -/
theorem cyclicCharacterCupMap_π
    (chi : G →* Multiplicative (ZMod 2))
    (A : Rep.{0} (ZMod 2) G) (n : ℕ)
    (z : cocycles A n) :
    (cyclicCharacterCupMap chi A n).hom (π A n z) =
      π A (n + 1) (cyclicCharacterCupCocycle chi A n z) := by
  let T := Rep.trivial (ZMod 2) G (ZMod 2)
  let t : cocycles (T ⊗ A) (n + 1) :=
    (((inhomogeneousCochains (T ⊗ A)).cyclesIsoOfEq
      (Nat.one_add n)).hom.hom
      (((inhomogeneousCupPairing G (ZMod 2) T A).pairCycles 1 n).hom
        (cyclicCharacterCocycle chi ⊗ₜ[ZMod 2] z)))
  unfold cyclicCharacterCupMap cupOneClassMap cyclicCharacterClass
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom, TensorProduct.mk_apply]
  have hCup := cupOneAny_π_apply T A n
    (cyclicCharacterCocycle chi) z
  have hCup' :
      cupOneAny (Rep.trivial (ZMod 2) G (ZMod 2)) A n
          ((π (Rep.trivial (ZMod 2) G (ZMod 2)) 1).hom
              (cyclicCharacterCocycle chi) ⊗ₜ[ZMod 2]
            (π A n).hom z) =
        (π (Rep.trivial (ZMod 2) G (ZMod 2) ⊗ A) (n + 1)).hom t := by
    simpa only [T] using hCup
  have hMap := ConcreteCategory.congr_hom
    (groupCohomology.π_map (MonoidHom.id G) (λ_ A).hom (n + 1)) t
  calc
    (groupCohomology.map (MonoidHom.id G)
        (λ_ A).hom (n + 1)).hom
        ((cupOneAny (Rep.trivial (ZMod 2) G (ZMod 2)) A n).hom
          ((π (Rep.trivial (ZMod 2) G (ZMod 2)) 1).hom
              (cyclicCharacterCocycle chi) ⊗ₜ[ZMod 2]
            (π A n).hom z)) =
      (groupCohomology.map (MonoidHom.id G)
        (λ_ A).hom (n + 1)).hom
        ((π (T ⊗ A) (n + 1)).hom t) :=
          congrArg (groupCohomology.map (MonoidHom.id G)
            (λ_ A).hom (n + 1)).hom hCup'
    _ = (π A (n + 1)).hom
        (HomologicalComplex.cyclesMap
          (cochainsMap (MonoidHom.id G) (λ_ A).hom) (n + 1) t) := hMap
    _ = (π A (n + 1)).hom
        (cyclicCharacterCupCocycleViaCup chi A n z) := rfl
    _ = (π A (n + 1)).hom
        (cyclicCharacterCupCocycle chi A n z) := by
          rw [cyclicCharacterCupCocycleViaCup_eq]

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary cyclic-permutation connecting morphism is cup product
with the cyclic character in every degree. -/
theorem cyclicPermutationTwo_delta_eq_cyclicCharacterCupMap
    (chi : G →* Multiplicative (ZMod 2))
    (A : Rep.{0} (ZMod 2) G) (n : ℕ) :
    δ (Rep.cyclicPermutationTwoShortComplex_shortExact chi A)
        n (n + 1) rfl =
      cyclicCharacterCupMap chi A n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  refine groupCohomology_induction_on x ?_
  intro z
  change (δ (Rep.cyclicPermutationTwoShortComplex_shortExact chi A)
      n (n + 1) rfl).hom ((π A n).hom z) =
    (cyclicCharacterCupMap chi A n).hom ((π A n).hom z)
  rw [cyclicPermutationTwo_delta_π, cyclicCharacterCupMap_π]

-- Naturality is checked on arbitrary cocycle representatives.
set_option backward.isDefEq.respectTransparency false in
/-- Cup with the cyclic character is natural simultaneously in the group
and the coefficient representation. -/
theorem cyclicCharacterCupMap_naturality
    {J : Type} [Group J] (f : J →* G)
    (chi : G →* Multiplicative (ZMod 2))
    {A : Rep.{0} (ZMod 2) G} {B : Rep.{0} (ZMod 2) J}
    (phi : Rep.res f A ⟶ B) (n : ℕ) :
    cyclicCharacterCupMap chi A n ≫
        groupCohomology.map f phi (n + 1) =
      groupCohomology.map f phi n ≫
        cyclicCharacterCupMap (chi.comp f) B n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  refine groupCohomology_induction_on x ?_
  intro z
  let zJ := HomologicalComplex.cyclesMap (cochainsMap f phi) n z
  have hmZ := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (cochainsMap f phi) n) z
  simp only [ConcreteCategory.comp_apply] at hmZ
  have hCycles :
      HomologicalComplex.cyclesMap (cochainsMap f phi) (n + 1)
          (cyclicCharacterCupCocycle chi A n z) =
        cyclicCharacterCupCocycle (chi.comp f) B n zJ := by
    apply (ModuleCat.mono_iff_injective (iCocycles B (n + 1))).mp
      inferInstance
    have hmCup := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i
        (cochainsMap f phi) (n + 1))
      (cyclicCharacterCupCocycle chi A n z)
    simp only [ConcreteCategory.comp_apply] at hmCup
    rw [hmCup]
    funext q
    change phi.hom
        ((iCocycles A (n + 1)).hom
          (cyclicCharacterCupCocycle chi A n z) (fun i => f (q i))) =
      (iCocycles B (n + 1)).hom
        (cyclicCharacterCupCocycle (chi.comp f) B n zJ) q
    rw [cyclicCharacterCupCocycle_apply,
      cyclicCharacterCupCocycle_apply]
    rw [hmZ]
    unfold cyclicCharacterCupCochain cyclicCharacterValue
    rw [map_smul]
    change Multiplicative.toAdd (chi (f (q 0))) •
        phi.hom (A.ρ (f (q 0))
          ((iCocycles A n).hom z (fun i => f (q i.succ)))) =
      Multiplicative.toAdd (chi (f (q 0))) •
        B.ρ (q 0)
          (phi.hom ((iCocycles A n).hom z
            (fun i => f (q i.succ))))
    exact congrArg
      (fun b : B => Multiplicative.toAdd (chi (f (q 0))) • b)
      (Rep.hom_comm_apply phi (q 0)
        ((iCocycles A n).hom z (fun i => f (q i.succ))))
  have hπn := ConcreteCategory.congr_hom
    (groupCohomology.π_map f phi n) z
  have hπs := ConcreteCategory.congr_hom
    (groupCohomology.π_map f phi (n + 1))
    (cyclicCharacterCupCocycle chi A n z)
  simp only [ConcreteCategory.comp_apply] at hπn hπs
  calc
    (groupCohomology.map f phi (n + 1)).hom
        ((cyclicCharacterCupMap chi A n).hom ((π A n).hom z)) =
      (groupCohomology.map f phi (n + 1)).hom
        ((π A (n + 1)).hom
          (cyclicCharacterCupCocycle chi A n z)) := by
            rw [cyclicCharacterCupMap_π]
    _ = (π B (n + 1)).hom
        (HomologicalComplex.cyclesMap (cochainsMap f phi) (n + 1)
          (cyclicCharacterCupCocycle chi A n z)) := hπs
    _ = (π B (n + 1)).hom
        (cyclicCharacterCupCocycle (chi.comp f) B n zJ) := by rw [hCycles]
    _ = (cyclicCharacterCupMap (chi.comp f) B n).hom
        ((π B n).hom zJ) := (cyclicCharacterCupMap_π _ _ _ _).symm
    _ = (cyclicCharacterCupMap (chi.comp f) B n).hom
        ((groupCohomology.map f phi n).hom ((π A n).hom z)) := by rw [hπn]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of cyclic-character cup followed by a compatible square of
source and target coefficient morphisms. -/
theorem cyclicCharacterCupMap_naturality_comp_coefficientSquare
    {J : Type} [Group J] (f : J →* G)
    (chi : G →* Multiplicative (ZMod 2))
    {A A' : Rep.{0} (ZMod 2) G}
    {B B' : Rep.{0} (ZMod 2) J}
    (phi : Rep.res f A ⟶ B) (phi' : Rep.res f A' ⟶ B')
    (s : A ⟶ A') (t : B ⟶ B')
    (hcoeff : (Rep.resFunctor f).map s ≫ phi' = phi ≫ t)
    (n : ℕ) :
    (groupCohomology.map f phi n ≫
        cyclicCharacterCupMap (chi.comp f) B n) ≫
      groupCohomology.map (MonoidHom.id J) t (n + 1) =
    (cyclicCharacterCupMap chi A n ≫
        groupCohomology.map (MonoidHom.id G) s (n + 1)) ≫
      groupCohomology.map f phi' (n + 1) := by
  let leftCoeff :=
    (Rep.resFunctor (MonoidHom.id J)).map phi ≫ t
  let rightCoeff := (Rep.resFunctor f).map s ≫ phi'
  have hgroup : f.comp (MonoidHom.id J) =
      (MonoidHom.id G).comp f := by
    ext j
    rfl
  have hlin : leftCoeff.hom.toLinearMap =
      rightCoeff.hom.toLinearMap := by
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom hcoeff.symm x
  have hmap : groupCohomology.map f phi (n + 1) ≫
        groupCohomology.map (MonoidHom.id J) t (n + 1) =
      groupCohomology.map (MonoidHom.id G) s (n + 1) ≫
        groupCohomology.map f phi' (n + 1) := by
    calc
      groupCohomology.map f phi (n + 1) ≫
          groupCohomology.map (MonoidHom.id J) t (n + 1) =
        groupCohomology.map (f.comp (MonoidHom.id J))
          leftCoeff (n + 1) :=
        (groupCohomology.map_comp f (MonoidHom.id J)
          phi t (n + 1)).symm
      _ = groupCohomology.map ((MonoidHom.id G).comp f)
          rightCoeff (n + 1) :=
        groupCohomology.map_congr hgroup hlin (n + 1)
      _ = groupCohomology.map (MonoidHom.id G) s (n + 1) ≫
          groupCohomology.map f phi' (n + 1) :=
        groupCohomology.map_comp (MonoidHom.id G) f s phi' (n + 1)
  have hcup := cyclicCharacterCupMap_naturality f chi phi n
  calc
    (groupCohomology.map f phi n ≫
          cyclicCharacterCupMap (chi.comp f) B n) ≫
        groupCohomology.map (MonoidHom.id J) t (n + 1) =
      (cyclicCharacterCupMap chi A n ≫
          groupCohomology.map f phi (n + 1)) ≫
        groupCohomology.map (MonoidHom.id J) t (n + 1) := by
          rw [hcup]
    _ = cyclicCharacterCupMap chi A n ≫
        (groupCohomology.map f phi (n + 1) ≫
          groupCohomology.map (MonoidHom.id J) t (n + 1)) := by
            simp only [Category.assoc]
    _ = cyclicCharacterCupMap chi A n ≫
        (groupCohomology.map (MonoidHom.id G) s (n + 1) ≫
          groupCohomology.map f phi' (n + 1)) := by rw [hmap]
    _ = (cyclicCharacterCupMap chi A n ≫
          groupCohomology.map (MonoidHom.id G) s (n + 1)) ≫
        groupCohomology.map f phi' (n + 1) := by
          simp only [Category.assoc]

end groupCohomology
