/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainComplex.PositiveTailMapFunctor
public import MathlibExt.Algebra.Homology.HomologicalComplex.MapHomologyIso

/-!
# Positive-tail homology and additive homology-preserving functors

Let K be a nonnegative chain complex in an abelian category with d_K,1,0 = 0. The comparison
H_n(T(K)) ≅ H_{n+1}(K) is induced by a map of the corresponding short complexes. Its first two
components are the identity reindexing maps; at n = 0 its last component is zero. For an
additive homology-preserving functor F between abelian categories, this comparison commutes with
T(F(K)) ≅ F(T(K)) and the canonical homology comparison H_n(F(K)) ≅ F(H_n(K)).
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace ChainComplex

variable {C : Type*} [Category* C] [Abelian C]

/-- Let C be abelian, K a nonnegative chain complex with d_K,1,0 = 0, and n a natural number. There
is a map from T(K)_{n+1} → T(K)_n → T(K)_{n−1} to K_{n+2} → K_{n+1} → K_n. Its first two
components are identities; the third is an identity when n > 0 and the zero map K₁ → K₀ when n =
0. Natural-number subtraction is used in n−1. -/
def positiveTailExplicitShortComplexMap (K : ChainComplex C ℕ) (hK : K.d 1 0 = 0) :
    ∀ n : ℕ, (positiveTail K).sc' (n + 1) n (n - 1) ⟶ K.sc' (n + 2) (n + 1) n
  | 0 =>
    { τ₁ := 𝟙 (K.X 2)
      τ₂ := 𝟙 (K.X 1)
      τ₃ := 0
      comm₁₂ := by
        change 𝟙 (K.X 2) ≫ K.d 2 1 = (positiveTail K).d 1 0 ≫ 𝟙 (K.X 1)
        exact (Category.id_comp _).trans
          ((positiveTail_d_succ K 0).symm.trans (Category.comp_id _).symm)
      comm₂₃ := by
        change 𝟙 (K.X 1) ≫ K.d 1 0 = (positiveTail K).d 0 0 ≫ 0
        exact (Category.id_comp _).trans (hK.trans (Limits.comp_zero).symm) }
  | n + 1 => (positiveTailRowIso K n).hom

/-- Let C be abelian, K a nonnegative chain complex with d_K,1,0 = 0, and n a natural number. The
canonical short-complex map T(K).sc(n) → K.sc(n+1) is obtained from the explicitly indexed
shifted-row map by the predecessor and successor reindexing isomorphisms. Its middle component
is the identity of K_{n+1}. -/
def positiveTailShortComplexMap (K : ChainComplex C ℕ) (hK : K.d 1 0 = 0) (n : ℕ) :
    (positiveTail K).sc n ⟶ K.sc (n + 1) :=
  ((positiveTail K).isoSc' (n + 1) n (n - 1) (by simp) (by cases n <;> simp)).hom ≫
    positiveTailExplicitShortComplexMap K hK n ≫
      (K.isoSc' (n + 2) (n + 1) n (by simp [Nat.add_assoc]) (by simp)).inv

/-- Let C be abelian, K a nonnegative chain complex with d_K,1,0 = 0, and n a natural number. Let
e_T identify T(K).sc(n) with its explicit row (n+1,n,n−1), and e_K identify K.sc(n+1) with its
row (n+2,n+1,n). The incoming component of positiveTailShortComplexMap is e_T.hom₁ ≫ e_K.inv₁,
the canonical identification of their degree-(n+2) terms. -/
theorem positiveTailShortComplexMap_τ₁ (K : ChainComplex C ℕ) (hK : K.d 1 0 = 0) (n : ℕ) :
    (positiveTailShortComplexMap K hK n).τ₁ =
      (((positiveTail K).isoSc' (n + 1) n (n - 1) (by simp) (by cases n <;> simp)).hom).τ₁ ≫
        ((K.isoSc' (n + 2) (n + 1) n (by simp [Nat.add_assoc]) (by simp)).inv).τ₁ := by
  let e₀ := (positiveTail K).isoSc' (n + 1) n (n - 1) (by simp) (by cases n <;> simp)
  let e₁ := K.isoSc' (n + 2) (n + 1) n (by simp [Nat.add_assoc]) (by simp)
  have ht : (positiveTailExplicitShortComplexMap K hK n).τ₁ = 𝟙 (K.X (n + 2)) := by
    cases n <;> rfl
  change e₀.hom.τ₁ ≫ (positiveTailExplicitShortComplexMap K hK n).τ₁ ≫ e₁.inv.τ₁ =
    e₀.hom.τ₁ ≫ e₁.inv.τ₁
  exact (congrArg (fun f : K.X (n + 2) ⟶ K.X (n + 2) => e₀.hom.τ₁ ≫ f ≫ e₁.inv.τ₁) ht).trans
    (congrArg (fun f => e₀.hom.τ₁ ≫ f) (Category.id_comp _))

/-- Let C be abelian, K a nonnegative chain complex with d_K,1,0 = 0, and n a natural number. The
middle component of positiveTailShortComplexMap K is the identity map of K_{n+1}. -/
theorem positiveTailShortComplexMap_τ₂ (K : ChainComplex C ℕ) (hK : K.d 1 0 = 0) (n : ℕ) :
    (positiveTailShortComplexMap K hK n).τ₂ = 𝟙 (K.X (n + 1)) := by
  let e₀ := (positiveTail K).isoSc' (n + 1) n (n - 1) (by simp) (by cases n <;> simp)
  let e₁ := K.isoSc' (n + 2) (n + 1) n (by simp [Nat.add_assoc]) (by simp)
  have h₀ : e₀.hom.τ₂ = 𝟙 (K.X (n + 1)) := rfl
  have h₁ : e₁.inv.τ₂ = 𝟙 (K.X (n + 1)) := rfl
  have ht : (positiveTailExplicitShortComplexMap K hK n).τ₂ = 𝟙 (K.X (n + 1)) := by
    cases n <;> rfl
  have hm : (positiveTailExplicitShortComplexMap K hK n).τ₂ ≫ e₁.inv.τ₂ = 𝟙 (K.X (n + 1)) :=
    (congrArg₂ (fun (f g : K.X (n + 1) ⟶ K.X (n + 1)) => f ≫ g) ht h₁).trans (Category.id_comp _)
  change e₀.hom.τ₂ ≫ (positiveTailExplicitShortComplexMap K hK n).τ₂ ≫ e₁.inv.τ₂ = _
  exact (congrArg₂ (fun (f g : K.X (n + 1) ⟶ K.X (n + 1)) => f ≫ g) h₀ hm).trans
    (Category.id_comp _)

/-- Let C be abelian, K a nonnegative chain complex with d_K,1,0 = 0, and n a natural number. The
forward map of H_n(T(K)) ≅ H_{n+1}(K) equals the homology map induced by
positiveTailShortComplexMap K : T(K).sc(n) → K.sc(n+1). -/
theorem positiveTailHomologyIso_hom_eq (K : ChainComplex C ℕ) (hK : K.d 1 0 = 0) (n : ℕ) :
    (positiveTailHomologyIso K hK n).hom =
      ShortComplex.homologyMap (positiveTailShortComplexMap K hK n) := by
  let θ := positiveTailShortComplexMap K hK n
  have hc : ShortComplex.cyclesMap θ = (positiveTailCyclesIso K hK n).hom := by
    apply (cancel_mono (K.iCycles (n + 1))).1
    exact (ShortComplex.cyclesMap_i θ).trans
      ((congrArg (fun f => (positiveTail K).iCycles n ≫ f)
        (positiveTailShortComplexMap_τ₂ K hK n)).trans
          ((Category.comp_id _).trans (positiveTailCyclesIso_i K hK n).symm))
  apply (cancel_epi ((positiveTail K).homologyπ n)).1
  symm
  exact (ShortComplex.homologyπ_naturality θ).trans
    ((congrArg (fun f => f ≫ K.homologyπ (n + 1)) hc).trans
      (positiveTailHomologyIso_π K hK n))

variable {D : Type*} [Category* D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]

omit [F.PreservesHomology] in
/-- Let C and D be abelian categories, F : C → D additive, and K a nonnegative chain complex with
d_K,1,0 = 0. The mapped complex F(K) also satisfies d_F(K),1,0 = 0. -/
theorem mapHomologicalComplex_d_one_zero (K : ChainComplex C ℕ) (hK : K.d 1 0 = 0) :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).d 1 0 = 0 := by
  change F.map (K.d 1 0) = 0
  rw [hK, F.map_zero]

/-- Let C and D be abelian, F : C → D additive and homology preserving, and K a nonnegative chain
complex with d_K,1,0 = 0. For n ∈ ℕ, let α_K : T(F(K)) ≅ F(T(K)), γ_n,K : H_n(F(K)) ≅ F(H_n(K)),
and e_K,n : H_n(T(K)) ≅ H_{n+1}(K) be the canonical comparisons. Then H_n(α_K.hom) ≫
γ_n,T(K).hom ≫ F(e_K,n.hom) = e_F(K),n.hom ≫ γ_{n+1,K}.hom. -/
@[reassoc]
theorem positiveTailHomologyIso_map (K : ChainComplex C ℕ) (hK : K.d 1 0 = 0) (n : ℕ) :
    HomologicalComplex.homologyMap ((positiveTailMapFunctorIso F).app K).hom n ≫
        ((F.mapHomologicalComplexHomologyIso (ComplexShape.down ℕ) n).app (positiveTail K)).hom ≫
          F.map (positiveTailHomologyIso K hK n).hom =
      (positiveTailHomologyIso ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K)
        (mapHomologicalComplex_d_one_zero F K hK) n).hom ≫
          ((F.mapHomologicalComplexHomologyIso (ComplexShape.down ℕ) (n + 1)).app K).hom := by
  let E := F.mapHomologicalComplex (ComplexShape.down ℕ)
  let e := (positiveTailMapFunctorIso F).app K
  let θ := positiveTailShortComplexMap K hK n
  let θF := positiveTailShortComplexMap (E.obj K) (mapHomologicalComplex_d_one_zero F K hK) n
  let a := (HomologicalComplex.shortComplexFunctor D (ComplexShape.down ℕ) n).map e.hom
  let S := (positiveTail (E.obj K)).sc n
  let T := F.mapShortComplex.obj (K.sc (n + 1))
  let b : S ⟶ T := a ≫ F.mapShortComplex.map θ
  have he (j : ℕ) : e.hom.f j = 𝟙 (F.obj (K.X (j + 1))) := rfl
  have hτ : b.τ₂ = θF.τ₂ := by
    change e.hom.f n ≫ F.map θ.τ₂ = θF.τ₂
    have hm : F.map θ.τ₂ = 𝟙 (F.obj (K.X (n + 1))) :=
      (congrArg F.map (positiveTailShortComplexMap_τ₂ K hK n)).trans (F.map_id _)
    exact (congrArg₂
      (fun (f g : F.obj (K.X (n + 1)) ⟶ F.obj (K.X (n + 1))) => f ≫ g)
      (he n) hm).trans ((Category.id_comp _).trans
        (positiveTailShortComplexMap_τ₂ (E.obj K) (mapHomologicalComplex_d_one_zero F K hK) n).symm)
  have hc : ShortComplex.cyclesMap b = ShortComplex.cyclesMap θF := by
    apply (cancel_mono T.iCycles).1
    exact (ShortComplex.cyclesMap_i b).trans
      ((congrArg (fun f => S.iCycles ≫ f) hτ).trans (ShortComplex.cyclesMap_i θF).symm)
  have hb : ShortComplex.homologyMap b = ShortComplex.homologyMap θF := by
    apply (cancel_epi S.homologyπ).1
    exact (ShortComplex.homologyπ_naturality b).trans
      ((congrArg (fun f => f ≫ T.homologyπ) hc).trans (ShortComplex.homologyπ_naturality θF).symm)
  have hH : ShortComplex.homologyMap a ≫ ShortComplex.homologyMap (F.mapShortComplex.map θ) =
      ShortComplex.homologyMap θF := (ShortComplex.homologyMap_comp _ _).symm.trans hb
  have hNat := ShortComplex.mapHomologyIso_hom_naturality θ F
  rw [positiveTailHomologyIso_hom_eq, positiveTailHomologyIso_hom_eq]
  change ShortComplex.homologyMap a ≫
      (((positiveTail K).sc n).mapHomologyIso F).hom ≫ F.map (ShortComplex.homologyMap θ) =
    ShortComplex.homologyMap θF ≫ ((K.sc (n + 1)).mapHomologyIso F).hom
  exact (congrArg (fun f => ShortComplex.homologyMap a ≫ f) hNat.symm).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun f => f ≫ ((K.sc (n + 1)).mapHomologyIso F).hom) hH))

end ChainComplex
