/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Monoidal.Limits.Cokernels
public import MathlibExt.Algebra.Homology.CochainChainGradedPairing
public import MathlibExt.Algebra.Homology.TensorHomologyDesc

/-!
# Descending cochain–chain pairings to homology

Let C be a preadditive monoidal category with additive tensor functors. A cochain–chain
pairing P_{p,q} : K^p⊗L_{p+q} → M_q sends cocycle–cycle tensors to cycles. Pairing a cocycle
with a chain boundary gives (−1)^p times an output boundary; pairing a cochain differential
with a cycle gives (−1)^{p+1} times an output boundary.

Put n=p+q and p⁻=(up ℕ).prev(p). Assume homology for K at p, L at n, and M at q, and the
binary coproduct of K^{p⁻}⊗Z_n(L) and Z^p(K)⊗L_{n+1}. For the boundary-to-cycles maps κ :
K^{p⁻} → Z^p(K) and λ : L_{n+1} → Z_n(L), assume H^p(K)⊗− preserves the cokernel of λ, and
−⊗Z_n(L) and −⊗L_{n+1} preserve the cokernel of κ. The pairing then descends to H^p(K)⊗H_n(L)
→ H_q(M).

A local input-boundary comparison gives equality of output homology classes when its tensor
product with Z^p(K) is epic.
-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory

namespace HomologicalComplex.CochainChainGradedPairing

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  {K : CochainComplex C ℕ} {L M : ChainComplex C ℕ}

private lemma negOnePow_mul_self (p : ℕ) :
    ((-1 : ℤ) ^ p) * ((-1 : ℤ) ^ p) = 1 := by
  rw [← pow_add, ← two_mul]
  simp

/-- Let C be preadditive and monoidal with additive tensor functors, P a cochain–chain pairing,
and p,q ∈ ℕ. Assume K has homology at p. Then (i_ZK⊗d_L)≫P_{p,q} =
(-1)^p·((i_ZK⊗id)≫P_{p,q+1}≫d_M). The source is Z^p(K)⊗L_{p+(q+1)}, the target is M_q, and d_L
maps to L_{p+q}. -/
lemma pair_chainBoundary_eq_boundary
    (P : CochainChainGradedPairing K L M) (p q : ℕ)
    [K.HasHomology p] :
    (K.iCycles p ⊗ₘ L.d (p + (q + 1)) (p + q)) ≫ P.pair p q =
      ((-1 : ℤ) ^ p) •
        ((K.iCycles p ▷ L.X (p + (q + 1))) ≫ P.pair p (q + 1) ≫
          M.d (q + 1) q) := by
  have h := congrArg
    (fun f => (K.iCycles p ⊗ₘ 𝟙 (L.X (p + (q + 1)))) ≫ f)
    (P.boundary p q)
  simp only [Preadditive.comp_zsmul, Preadditive.comp_sub, ← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id,
    K.iCycles_d] at h
  simp only [tensorHom_id, Category.assoc, Int.reduceNeg, Category.id_comp,
    MonoidalPreadditive.zero_tensor, zero_comp, sub_zero] at h
  calc
    (K.iCycles p ⊗ₘ L.d (p + (q + 1)) (p + q)) ≫ P.pair p q =
        ((-1 : ℤ) ^ p) • ((-1 : ℤ) ^ p) •
          ((K.iCycles p ⊗ₘ L.d (p + (q + 1)) (p + q)) ≫ P.pair p q) := by
            rw [smul_smul, negOnePow_mul_self, one_smul]
    _ = ((-1 : ℤ) ^ p) •
        ((K.iCycles p ▷ L.X (p + (q + 1))) ≫ P.pair p (q + 1) ≫
          M.d (q + 1) q) := by
            rw [← h]

/-- Let C be preadditive and monoidal with additive tensor functors, and assume homology for K at
p, L at p+q, and M at q. For v : V → A, z₁,z₂ : A → Z_{p+q}(L), and b : V → L_{p+(q+1)},
suppose v≫(z₁−z₂)≫i_ZL=b≫d_L. Set c_i=(id_ZK⊗z_i)≫P.pairCycles and
b_out=(-1)^p·((i_ZK⊗b)≫P_{p,q+1}). Then (id_ZK⊗v)≫(c₁−c₂)≫i_ZM=b_out≫d_M. No epimorphism
hypothesis is required for this local equality. -/
lemma pair_inputBoundary_to_outputBoundary
    (P : CochainChainGradedPairing K L M) (p q : ℕ)
    [K.HasHomology p] [L.HasHomology (p + q)] [M.HasHomology q]
    {A V : C} (v : V ⟶ A)
    (z₁ z₂ : A ⟶ L.cycles (p + q))
    (b : V ⟶ L.X (p + (q + 1)))
    (hb :
      v ≫ ((z₁ - z₂) ≫ L.iCycles (p + q)) =
        b ≫ L.d (p + (q + 1)) (p + q)) :
    let c₁ := (𝟙 (K.cycles p) ⊗ₘ z₁) ≫ P.pairCycles p q
    let c₂ := (𝟙 (K.cycles p) ⊗ₘ z₂) ≫ P.pairCycles p q
    let bOut :=
      ((-1 : ℤ) ^ p) •
        ((K.iCycles p ⊗ₘ b) ≫ P.pair p (q + 1))
    (𝟙 (K.cycles p) ⊗ₘ v) ≫
        ((c₁ - c₂) ≫ M.iCycles q) =
      bOut ≫ M.d (q + 1) q := by
  intro c₁ c₂ bOut
  have hc₁ :
      c₁ ≫ M.iCycles q =
        (𝟙 (K.cycles p) ⊗ₘ z₁) ≫
          (K.iCycles p ⊗ₘ L.iCycles (p + q)) ≫ P.pair p q := by
    dsimp only [c₁]
    simp only [Category.assoc, P.pairCycles_i]
  have hc₂ :
      c₂ ≫ M.iCycles q =
        (𝟙 (K.cycles p) ⊗ₘ z₂) ≫
          (K.iCycles p ⊗ₘ L.iCycles (p + q)) ≫ P.pair p q := by
    dsimp only [c₂]
    simp only [Category.assoc, P.pairCycles_i]
  have hNeg : ∀ g : V ⟶ L.X (p + q),
      K.iCycles p ⊗ₘ (-g) = -(K.iCycles p ⊗ₘ g) := by
    intro g
    have hzero :
        (K.iCycles p ⊗ₘ (-g)) + (K.iCycles p ⊗ₘ g) = 0 := by
      rw [← MonoidalPreadditive.tensor_add, neg_add_cancel,
        MonoidalPreadditive.tensor_zero]
    exact eq_neg_of_add_eq_zero_left hzero
  have hTensorSub :
      K.iCycles p ⊗ₘ
          (v ≫ ((z₁ - z₂) ≫ L.iCycles (p + q))) =
        (K.iCycles p ⊗ₘ
            (v ≫ (z₁ ≫ L.iCycles (p + q)))) -
          (K.iCycles p ⊗ₘ
            (v ≫ (z₂ ≫ L.iCycles (p + q)))) := by
    rw [Preadditive.sub_comp, Preadditive.comp_sub, sub_eq_add_neg,
      MonoidalPreadditive.tensor_add, hNeg, ← sub_eq_add_neg]
  have hBoundary := congrArg
    (fun m => (𝟙 (K.cycles p) ⊗ₘ b) ≫ m)
    (P.pair_chainBoundary_eq_boundary p q)
  rw [← MonoidalCategory.tensorHom_id] at hBoundary
  simp only [Preadditive.comp_zsmul, ← Category.assoc] at hBoundary
  rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp,
    Category.comp_id] at hBoundary
  calc
    (𝟙 (K.cycles p) ⊗ₘ v) ≫
          ((c₁ - c₂) ≫ M.iCycles q) =
        (𝟙 (K.cycles p) ⊗ₘ v) ≫
          ((c₁ ≫ M.iCycles q) - (c₂ ≫ M.iCycles q)) := by
      rw [Preadditive.sub_comp]
    _ = ((𝟙 (K.cycles p) ⊗ₘ v) ≫
          (c₁ ≫ M.iCycles q)) -
        ((𝟙 (K.cycles p) ⊗ₘ v) ≫
          (c₂ ≫ M.iCycles q)) := by
      rw [Preadditive.comp_sub]
    _ = ((K.iCycles p ⊗ₘ
            (v ≫ (z₁ ≫ L.iCycles (p + q)))) ≫ P.pair p q) -
        ((K.iCycles p ⊗ₘ
            (v ≫ (z₂ ≫ L.iCycles (p + q)))) ≫ P.pair p q) := by
      rw [hc₁, hc₂]
      simp only [← Category.assoc]
      rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp,
        MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp,
        MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp,
        MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
    _ = (K.iCycles p ⊗ₘ
          (v ≫ ((z₁ - z₂) ≫ L.iCycles (p + q)))) ≫
        P.pair p q := by
      rw [← Preadditive.sub_comp, ← hTensorSub]
    _ = (K.iCycles p ⊗ₘ
          (b ≫ L.d (p + (q + 1)) (p + q))) ≫ P.pair p q := by
      rw [hb]
    _ = bOut ≫ M.d (q + 1) q := by
      dsimp only [bOut]
      simpa only [Preadditive.zsmul_comp, Category.assoc] using hBoundary

/-- Let C be preadditive and monoidal with additive tensor functors, P a pairing, and assume
homology for K at p, L at p+q, and M at q. Let v : V → A and cycles z₁,z₂ : A → Z_{p+q}(L)
differ by a boundary after v: v≫(z₁−z₂)≫i_ZL=b≫d_L for b : V → L_{p+(q+1)}. If id_{Z^p(K)}⊗v
is epic, then (id⊗z₁)≫P.pairCycles≫π_M=(id⊗z₂)≫P.pairCycles≫π_M. Thus the paired cycles have
the same output homology class. -/
public lemma pairCycles_comp_homologyπ_eq_of_epi_inputBoundary
    (P : CochainChainGradedPairing K L M) (p q : ℕ)
    [K.HasHomology p] [L.HasHomology (p + q)] [M.HasHomology q]
    {A V : C} (v : V ⟶ A)
    (z₁ z₂ : A ⟶ L.cycles (p + q))
    (b : V ⟶ L.X (p + (q + 1)))
    [Epi (𝟙 (K.cycles p) ⊗ₘ v)]
    (hb :
      v ≫ ((z₁ - z₂) ≫ L.iCycles (p + q)) =
        b ≫ L.d (p + (q + 1)) (p + q)) :
    ((𝟙 (K.cycles p) ⊗ₘ z₁) ≫ P.pairCycles p q) ≫
        M.homologyπ q =
      ((𝟙 (K.cycles p) ⊗ₘ z₂) ≫ P.pairCycles p q) ≫
        M.homologyπ q := by
  let pre := 𝟙 (K.cycles p) ⊗ₘ v
  let c₁ := (𝟙 (K.cycles p) ⊗ₘ z₁) ≫ P.pairCycles p q
  let c₂ := (𝟙 (K.cycles p) ⊗ₘ z₂) ≫ P.pairCycles p q
  let bOut :=
    ((-1 : ℤ) ^ p) •
      ((K.iCycles p ⊗ₘ b) ≫ P.pair p (q + 1))
  have hBoundary :=
    P.pair_inputBoundary_to_outputBoundary p q v z₁ z₂ b hb
  change pre ≫ ((c₁ - c₂) ≫ M.iCycles q) =
    bOut ≫ M.d (q + 1) q at hBoundary
  have hCycles : pre ≫ (c₁ - c₂) =
      bOut ≫ M.toCycles (q + 1) q := by
    apply (cancel_mono (M.iCycles q)).1
    calc
      (pre ≫ (c₁ - c₂)) ≫ M.iCycles q =
          pre ≫ ((c₁ - c₂) ≫ M.iCycles q) :=
        Category.assoc _ _ _
      _ = bOut ≫ M.d (q + 1) q := hBoundary
      _ = bOut ≫
          (M.toCycles (q + 1) q ≫ M.iCycles q) :=
        congrArg (fun m => bOut ≫ m) (M.toCycles_i (q + 1) q).symm
      _ = (bOut ≫ M.toCycles (q + 1) q) ≫ M.iCycles q :=
        (Category.assoc _ _ _).symm
  have hCyclesHom := congrArg (fun m => m ≫ M.homologyπ q) hCycles
  have hDiffZero : (pre ≫ (c₁ - c₂)) ≫ M.homologyπ q = 0 := by
    calc
      (pre ≫ (c₁ - c₂)) ≫ M.homologyπ q =
          (bOut ≫ M.toCycles (q + 1) q) ≫ M.homologyπ q :=
        hCyclesHom
      _ = bOut ≫
          (M.toCycles (q + 1) q ≫ M.homologyπ q) :=
        Category.assoc _ _ _
      _ = 0 := by rw [M.toCycles_comp_homologyπ, comp_zero]
  have hPre : pre ≫ (c₁ ≫ M.homologyπ q) =
      pre ≫ (c₂ ≫ M.homologyπ q) := by
    apply sub_eq_zero.mp
    calc
      pre ≫ (c₁ ≫ M.homologyπ q) -
            pre ≫ (c₂ ≫ M.homologyπ q) =
          pre ≫ ((c₁ - c₂) ≫ M.homologyπ q) := by
        simp only [Preadditive.sub_comp, Preadditive.comp_sub]
      _ = (pre ≫ (c₁ - c₂)) ≫ M.homologyπ q :=
        (Category.assoc _ _ _).symm
      _ = 0 := hDiffZero
  change c₁ ≫ M.homologyπ q = c₂ ≫ M.homologyπ q
  apply (cancel_epi pre).1
  exact hPre

/-- For a cochain–chain pairing P in a preadditive monoidal category with additive tensor
functors, assume homology for K at p and M at q. The composite
(i_ZK⊗d_L)≫P_{p,q}≫pOpcycles_M,q is zero, with source Z^p(K)⊗L_{p+q+1}. Pairing a cocycle with
an incoming chain boundary gives an output boundary, which the opcycles projection kills. -/
lemma cycles_opcycles_desc_kill
    (P : CochainChainGradedPairing K L M) (p q : ℕ)
    [K.HasHomology p] [M.HasHomology q] :
    (K.iCycles p ⊗ₘ L.d ((p + q) + 1) (p + q)) ≫
      P.pair p q ≫ M.pOpcycles q = 0 := by
  have hdeg : ((p + q) + 1) = p + (q + 1) := by omega
  rw [hdeg, ← Category.assoc, P.pair_chainBoundary_eq_boundary]
  simp only [Preadditive.zsmul_comp, Category.assoc, M.d_pOpcycles, comp_zero,
    smul_zero]

private lemma right_boundary
    (P : CochainChainGradedPairing K L M) (p q : ℕ)
    [K.HasHomology p] [L.HasHomology (p + q)] [M.HasHomology q] :
    ((K.cycles p ◁ L.toCycles (p + (q + 1)) (p + q)) ≫
        P.pairCycles p q) ≫ M.homologyπ q = 0 := by
  have hto :
      (K.cycles p ◁ L.toCycles (p + (q + 1)) (p + q)) ≫
          (K.iCycles p ⊗ₘ L.iCycles (p + q)) =
        K.iCycles p ⊗ₘ L.d (p + (q + 1)) (p + q) := by
    calc
      _ = (𝟙 (K.cycles p) ⊗ₘ L.toCycles (p + (q + 1)) (p + q)) ≫
          (K.iCycles p ⊗ₘ L.iCycles (p + q)) := by
            simp [MonoidalCategory.tensorHom_def']
      _ = K.iCycles p ⊗ₘ
          (L.toCycles (p + (q + 1)) (p + q) ≫ L.iCycles (p + q)) := by
            rw [MonoidalCategory.tensorHom_comp_tensorHom]
            simp
      _ = _ := by rw [L.toCycles_i]
  rw [pairCycles, M.comp_liftCycles]
  let x : K.cycles p ⊗ L.X (p + (q + 1)) ⟶ M.X (q + 1) :=
    ((-1 : ℤ) ^ p) •
      ((K.iCycles p ▷ L.X (p + (q + 1))) ≫ P.pair p (q + 1))
  apply M.liftCycles_homologyπ_eq_zero_of_boundary _ _ _ x
  rw [← Category.assoc, hto]
  dsimp only [x]
  simpa only [Preadditive.zsmul_comp, Category.assoc] using
    P.pair_chainBoundary_eq_boundary p q

/-- Let C be preadditive and monoidal with additive tensor functors, P a cochain–chain pairing,
and assume L has homology at (p+1)+q. If e : L_{(p+1)+q} ≅ L_{p+(q+1)}, then
(d_K⊗i_ZL)≫P_{p+1,q} = (-1)^{p+1}·((id⊗(i_ZL≫e.hom))≫P_{p,q+1}≫d_M). The source is
K^p⊗Z_{(p+1)+q}(L), and the sign is (-1)^{p+1}. -/
lemma pair_cochainBoundary_eq_boundary
    (P : CochainChainGradedPairing K L M) (p q : ℕ)
    [L.HasHomology ((p + 1) + q)] :
    (K.d p (p + 1) ⊗ₘ L.iCycles ((p + 1) + q)) ≫ P.pair (p + 1) q =
      ((-1 : ℤ) ^ (p + 1)) •
        (((𝟙 (K.X p) ⊗ₘ (L.iCycles ((p + 1) + q) ≫
            (L.XIsoOfEq (show (p + 1) + q = p + (q + 1) by omega)).hom)) ≫
          P.pair p (q + 1) ≫ M.d (q + 1) q)) := by
  let e := L.XIsoOfEq (show (p + 1) + q = p + (q + 1) by omega)
  let pre : K.X p ⊗ L.cycles ((p + 1) + q) ⟶
      K.X p ⊗ L.X (p + (q + 1)) :=
    𝟙 (K.X p) ⊗ₘ (L.iCycles ((p + 1) + q) ≫ e.hom)
  have hleft :
      pre ≫ (𝟙 (K.X p) ⊗ₘ L.d (p + (q + 1)) (p + q)) = 0 := by
    dsimp only [pre]
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    dsimp only [e]
    simp only [Category.id_comp, Category.assoc]
    rw [L.XIsoOfEq_hom_comp_d, L.iCycles_d]
    simp
  have hright :
      pre ≫ (K.d p (p + 1) ⊗ₘ e.inv) =
        K.d p (p + 1) ⊗ₘ L.iCycles ((p + 1) + q) := by
    dsimp only [pre]
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    dsimp only [e]
    simp only [Category.id_comp]
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h := congrArg
    (fun f => pre ≫ f)
    (P.boundary p q)
  simp only [Preadditive.comp_zsmul, Preadditive.comp_sub] at h
  simp only [← Category.assoc] at h
  rw [hleft, hright] at h
  simp only [zero_comp, zero_sub] at h
  have h' :
      pre ≫ P.pair p (q + 1) ≫ M.d (q + 1) q =
        ((-1 : ℤ) ^ (p + 1)) •
          ((K.d p (p + 1) ⊗ₘ L.iCycles ((p + 1) + q)) ≫
            P.pair (p + 1) q) := by
    simpa only [Category.assoc, pow_succ, mul_neg, mul_one, neg_smul,
      smul_neg, Preadditive.zsmul_comp, Preadditive.neg_comp] using h
  calc
    (K.d p (p + 1) ⊗ₘ L.iCycles ((p + 1) + q)) ≫ P.pair (p + 1) q =
        ((-1 : ℤ) ^ (p + 1)) • ((-1 : ℤ) ^ (p + 1)) •
          ((K.d p (p + 1) ⊗ₘ L.iCycles ((p + 1) + q)) ≫
            P.pair (p + 1) q) := by
              rw [smul_smul, negOnePow_mul_self, one_smul]
    _ = ((-1 : ℤ) ^ (p + 1)) •
        (pre ≫ P.pair p (q + 1) ≫ M.d (q + 1) q) := by
          rw [← h']

private lemma left_boundary_succ
    (P : CochainChainGradedPairing K L M) (p q : ℕ)
    [K.HasHomology (p + 1)] [L.HasHomology ((p + 1) + q)] [M.HasHomology q] :
    ((K.toCycles p (p + 1) ▷ L.cycles ((p + 1) + q)) ≫
        P.pairCycles (p + 1) q) ≫ M.homologyπ q = 0 := by
  have hto :
      (K.toCycles p (p + 1) ▷ L.cycles ((p + 1) + q)) ≫
          (K.iCycles (p + 1) ⊗ₘ L.iCycles ((p + 1) + q)) =
        K.d p (p + 1) ⊗ₘ L.iCycles ((p + 1) + q) := by
    calc
      _ = (K.toCycles p (p + 1) ⊗ₘ 𝟙 (L.cycles ((p + 1) + q))) ≫
          (K.iCycles (p + 1) ⊗ₘ L.iCycles ((p + 1) + q)) := by
            simp [MonoidalCategory.tensorHom_def]
      _ = (K.toCycles p (p + 1) ≫ K.iCycles (p + 1)) ⊗ₘ
          L.iCycles ((p + 1) + q) := by
            rw [MonoidalCategory.tensorHom_comp_tensorHom]
            simp
      _ = _ := by rw [K.toCycles_i]
  rw [pairCycles, M.comp_liftCycles]
  let e := L.XIsoOfEq (show (p + 1) + q = p + (q + 1) by omega)
  let pre : K.X p ⊗ L.cycles ((p + 1) + q) ⟶
      K.X p ⊗ L.X (p + (q + 1)) :=
    𝟙 (K.X p) ⊗ₘ (L.iCycles ((p + 1) + q) ≫ e.hom)
  let x : K.X p ⊗ L.cycles ((p + 1) + q) ⟶ M.X (q + 1) :=
    ((-1 : ℤ) ^ (p + 1)) • (pre ≫ P.pair p (q + 1))
  apply M.liftCycles_homologyπ_eq_zero_of_boundary _ _ _ x
  rw [← Category.assoc, hto]
  dsimp only [x]
  dsimp only [pre, e]
  simpa only [Preadditive.zsmul_comp, Category.assoc] using
    P.pair_cochainBoundary_eq_boundary p q

private lemma left_boundary
    (P : CochainChainGradedPairing K L M) (p q : ℕ)
    [K.HasHomology p] [L.HasHomology (p + q)] [M.HasHomology q] :
    ((K.toCycles ((ComplexShape.up ℕ).prev p) p ▷ L.cycles (p + q)) ≫
        P.pairCycles p q) ≫ M.homologyπ q = 0 := by
  cases p with
  | zero =>
      rw [CochainComplex.prev_nat_zero, K.toCycles_eq_zero (by simp [ComplexShape.up])]
      simp
  | succ p =>
      rw [CochainComplex.prev_nat_succ]
      exact P.left_boundary_succ p q

@[reassoc]
lemma boundaries_comp_homologyπ
    (P : CochainChainGradedPairing K L M) (p q : ℕ)
    [K.HasHomology p] [L.HasHomology (p + q)] [M.HasHomology q]
    [HasBinaryCoproduct
      (K.X ((ComplexShape.up ℕ).prev p) ⊗ L.cycles (p + q))
      (K.cycles p ⊗ L.X (p + (q + 1)))] :
    Limits.coprod.desc
        (K.toCycles ((ComplexShape.up ℕ).prev p) p ▷ L.cycles (p + q))
        (K.cycles p ◁ L.toCycles (p + (q + 1)) (p + q)) ≫
      P.pairCycles p q ≫ M.homologyπ q = 0 := by
  apply Limits.coprod.hom_ext
  · rw [Limits.coprod.inl_desc_assoc, comp_zero]
    simpa only [Category.assoc] using P.left_boundary p q
  · rw [Limits.coprod.inr_desc_assoc, comp_zero]
    simpa only [Category.assoc] using P.right_boundary p q

/-- Let C be preadditive and monoidal with additive tensor functors, P a pairing, n=p+q, and
p⁻=(up ℕ).prev(p). Assume homology for K at p, L at n, and M at q, and the binary coproduct of
K^{p⁻}⊗Z_n(L) and Z^p(K)⊗L_{n+1}. Let κ : K^{p⁻} → Z^p(K) and λ : L_{n+1} → Z_n(L) be the
boundary-to-cycles maps. Assume H^p(K)⊗− preserves the cokernel of λ, while −⊗Z_n(L) and
−⊗L_{n+1} preserve the cokernel of κ. Then the cycle pairing followed by π_M descends to
H^p(K)⊗H_n(L) → H_q(M). -/
noncomputable def pairHomology
    (P : CochainChainGradedPairing K L M) (p q : ℕ)
    [K.HasHomology p] [L.HasHomology (p + q)] [M.HasHomology q]
    [HasBinaryCoproduct
      (K.X ((ComplexShape.up ℕ).prev p) ⊗ L.cycles (p + q))
      (K.cycles p ⊗ L.X (p + (q + 1)))]
    [PreservesColimit
      (parallelPair (L.toCycles (p + (q + 1)) (p + q)) 0)
      (tensorLeft (K.homology p))]
    [PreservesColimit
      (parallelPair (K.toCycles ((ComplexShape.up ℕ).prev p) p) 0)
      (tensorRight (L.cycles (p + q)))]
    [PreservesColimit
      (parallelPair (K.toCycles ((ComplexShape.up ℕ).prev p) p) 0)
      (tensorRight (L.X (p + (q + 1))))] :
    K.homology p ⊗ L.homology (p + q) ⟶ M.homology q :=
  HomologicalComplex.tensorHomologyDesc
    K ((ComplexShape.up ℕ).prev p) p rfl
    L (p + (q + 1)) (p + q) (by
      simp only [ChainComplex.prev]
      omega)
    (P.pairCycles p q ≫ M.homologyπ q)
    (P.boundaries_comp_homologyπ p q)

@[reassoc (attr := simp)]
lemma tensor_homologyπ_comp_pairHomology
    (P : CochainChainGradedPairing K L M) (p q : ℕ)
    [K.HasHomology p] [L.HasHomology (p + q)] [M.HasHomology q]
    [HasBinaryCoproduct
      (K.X ((ComplexShape.up ℕ).prev p) ⊗ L.cycles (p + q))
      (K.cycles p ⊗ L.X (p + (q + 1)))]
    [PreservesColimit
      (parallelPair (L.toCycles (p + (q + 1)) (p + q)) 0)
      (tensorLeft (K.homology p))]
    [PreservesColimit
      (parallelPair (K.toCycles ((ComplexShape.up ℕ).prev p) p) 0)
      (tensorRight (L.cycles (p + q)))]
    [PreservesColimit
      (parallelPair (K.toCycles ((ComplexShape.up ℕ).prev p) p) 0)
      (tensorRight (L.X (p + (q + 1))))] :
    (K.homologyπ p ⊗ₘ L.homologyπ (p + q)) ≫ P.pairHomology p q =
      P.pairCycles p q ≫ M.homologyπ q :=
  HomologicalComplex.tensor_homologyπ_comp_tensorHomologyDesc
    K ((ComplexShape.up ℕ).prev p) p rfl
    L (p + (q + 1)) (p + q) (by
      simp only [ChainComplex.prev]
      omega)
    (P.pairCycles p q ≫ M.homologyπ q)
    (P.boundaries_comp_homologyπ p q)

lemma tensor_homologyπ_hom_ext {A : C} (p q : ℕ)
    [K.HasHomology p] [L.HasHomology (p + q)]
    [PreservesColimit
      (parallelPair (L.toCycles (p + (q + 1)) (p + q)) 0)
      (tensorLeft (K.homology p))]
    [PreservesColimit
      (parallelPair (K.toCycles ((ComplexShape.up ℕ).prev p) p) 0)
      (tensorRight (L.cycles (p + q)))]
    {f g : K.homology p ⊗ L.homology (p + q) ⟶ A}
    (h : (K.homologyπ p ⊗ₘ L.homologyπ (p + q)) ≫ f =
      (K.homologyπ p ⊗ₘ L.homologyπ (p + q)) ≫ g) : f = g :=
  HomologicalComplex.tensor_homologyπ_hom_ext
    K ((ComplexShape.up ℕ).prev p) p rfl
    L (p + (q + 1)) (p + q) (by
      simp only [ChainComplex.prev]
      omega) h

@[reassoc]
lemma pairCycles_naturality
    {K' : CochainComplex C ℕ} {L' M' : ChainComplex C ℕ}
    (P : CochainChainGradedPairing K L M)
    (Q : CochainChainGradedPairing K' L' M')
    (fK : K ⟶ K') (fL : L ⟶ L') (fM : M ⟶ M')
    (hpair : ∀ p q, P.pair p q ≫ fM.f q =
      (fK.f p ⊗ₘ fL.f (p + q)) ≫ Q.pair p q)
    (p q : ℕ)
    [K.HasHomology p] [L.HasHomology (p + q)] [M.HasHomology q]
    [K'.HasHomology p] [L'.HasHomology (p + q)] [M'.HasHomology q] :
    (K.cyclesMap fK p ⊗ₘ L.cyclesMap fL (p + q)) ≫ Q.pairCycles p q =
      P.pairCycles p q ≫ M.cyclesMap fM q := by
  rw [← cancel_mono (M'.iCycles q)]
  simp only [Category.assoc]
  rw [Q.pairCycles_i, cyclesMap_i, P.pairCycles_i_assoc]
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc, cyclesMap_i, cyclesMap_i]
  rw [← MonoidalCategory.tensorHom_comp_tensorHom_assoc, hpair]

lemma pairHomology_naturality
    {K' : CochainComplex C ℕ} {L' M' : ChainComplex C ℕ}
    (P : CochainChainGradedPairing K L M)
    (Q : CochainChainGradedPairing K' L' M')
    (fK : K ⟶ K') (fL : L ⟶ L') (fM : M ⟶ M')
    (hpair : ∀ p q, P.pair p q ≫ fM.f q =
      (fK.f p ⊗ₘ fL.f (p + q)) ≫ Q.pair p q)
    (p q : ℕ)
    [K.HasHomology p] [L.HasHomology (p + q)] [M.HasHomology q]
    [K'.HasHomology p] [L'.HasHomology (p + q)] [M'.HasHomology q]
    [HasBinaryCoproduct
      (K.X ((ComplexShape.up ℕ).prev p) ⊗ L.cycles (p + q))
      (K.cycles p ⊗ L.X (p + (q + 1)))]
    [PreservesColimit
      (parallelPair (L.toCycles (p + (q + 1)) (p + q)) 0)
      (tensorLeft (K.homology p))]
    [PreservesColimit
      (parallelPair (K.toCycles ((ComplexShape.up ℕ).prev p) p) 0)
      (tensorRight (L.cycles (p + q)))]
    [PreservesColimit
      (parallelPair (K.toCycles ((ComplexShape.up ℕ).prev p) p) 0)
      (tensorRight (L.X (p + (q + 1))))]
    [HasBinaryCoproduct
      (K'.X ((ComplexShape.up ℕ).prev p) ⊗ L'.cycles (p + q))
      (K'.cycles p ⊗ L'.X (p + (q + 1)))]
    [PreservesColimit
      (parallelPair (L'.toCycles (p + (q + 1)) (p + q)) 0)
      (tensorLeft (K'.homology p))]
    [PreservesColimit
      (parallelPair (K'.toCycles ((ComplexShape.up ℕ).prev p) p) 0)
      (tensorRight (L'.cycles (p + q)))]
    [PreservesColimit
      (parallelPair (K'.toCycles ((ComplexShape.up ℕ).prev p) p) 0)
      (tensorRight (L'.X (p + (q + 1))))] :
    (K.homologyMap fK p ⊗ₘ L.homologyMap fL (p + q)) ≫ Q.pairHomology p q =
      P.pairHomology p q ≫ M.homologyMap fM q := by
  apply HomologicalComplex.tensorHomologyDesc_naturality
    K ((ComplexShape.up ℕ).prev p) p rfl
    L (p + (q + 1)) (p + q) (by
      simp only [ChainComplex.prev]
      omega) fK fL
    (P.pairCycles p q ≫ M.homologyπ q)
    (P.boundaries_comp_homologyπ p q)
    (Q.pairCycles p q ≫ M'.homologyπ q)
    (Q.boundaries_comp_homologyπ p q)
    (M.homologyMap fM q)
  rw [pairCycles_naturality_assoc P Q fK fL fM hpair]
  rw [← M.homologyπ_naturality fM]
  rw [Category.assoc]

end HomologicalComplex.CochainChainGradedPairing

end
