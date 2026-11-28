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

public import MathlibExt.Algebra.Homology.HomComplex.LinearFunctor

/-!
# Homotopies of linear product Hom-complex maps

Let R be a ring and C a preadditive R-linear category, with independent scalar, object and
morphism universes. For integer cochain complexes, precomposition and postcomposition are
composition of homogeneous cochains with the degree-zero cochain of the given complex map.

A target homotopy h:g₀≃g₁ gives the degree-minus-one operator H_n(z)=z≫h on the product Hom
complex. A source homotopy h:f₀≃f₁ gives H_n(z)=(-1)^n h≫z. The Hom differential of each
operator is the difference of the induced degree-zero maps. Thus homotopies in either complex
variable induce homotopies of the linear Hom-complex maps, on the full integer-indexed product
model.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory HomologicalComplex

namespace CochainComplex.HomComplex

universe uR uC vC

variable (R : Type uR) [Ring R]
  {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear R C]

/-- Let R be a ring in universe uR and C a preadditive R-linear category with independent object
universe uC and morphism universe vC. For integer cochain complexes P,L,L′, g:L→L′ and a
degree-n cochain z:P→L, the map induced by id_P,g equals z composed with the degree-zero cochain
of g. Its component is z_i≫g_{i+n}, and no extra degree sign is inserted. -/
theorem mapLinearOver_post {P L L' : CochainComplex C ℤ} (g : L ⟶ L')
    (n : ℤ) (z : Cochain P L n) :
    mapLinearOver R (𝟙 P) g n z = z.comp (Cochain.ofHom g) (add_zero n) := by
  apply Cochain.ext
  intro p q hpq
  simp only [mapLinearOver_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    HomologicalComplex.id_f, Category.id_comp]

/-- Let R be a ring in universe uR and C a preadditive R-linear category with independent object
universe uC and morphism universe vC. For integer cochain complexes P,P′,L, f:P′→P and a
degree-n cochain z:P→L, the map induced by f,id_L is the degree-zero cochain of f composed with
z. Its component is f_i≫z_i. -/
theorem mapLinearOver_pre {P P' L : CochainComplex C ℤ} (f : P' ⟶ P)
    (n : ℤ) (z : Cochain P L n) :
    mapLinearOver R f (𝟙 L) n z = (Cochain.ofHom f).comp z (zero_add n) := by
  apply Cochain.ext
  intro p q hpq
  simp only [mapLinearOver_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    HomologicalComplex.id_f, Category.comp_id]

/-- Let R be a ring in universe uR and C a preadditive R-linear category with independent object
universe uC and morphism universe vC. For a target homotopy h:g₀≃g₁ between maps L→L′ and fixed
integer cochain complex P, this degree-minus-one cochain from Hom(P,L) to Hom(P,L′) sends z of
degree n to z composed with the degree-minus-one cochain of h. It sends degree n to n−1 and has
component z_i≫h_{i+n}. -/
def linearPostHomotopyCochain (P : CochainComplex C ℤ)
    {L L' : CochainComplex C ℤ} {g₀ g₁ : L ⟶ L'} (h : Homotopy g₀ g₁) :
    Cochain (linearComplex R P L) (linearComplex R P L') (-1) :=
  Cochain.mk fun _n _m hnm => ModuleCat.ofHom
    { toFun := fun z => z.comp (Cochain.ofHomotopy h) hnm
      map_add' z z' := Cochain.add_comp z z' (Cochain.ofHomotopy h) hnm
      map_smul' r z := Cochain.smul_comp r z (Cochain.ofHomotopy h) hnm }

/-- Let R be a ring in universe uR and C a preadditive R-linear category with independent object
universe uC and morphism universe vC. For h:g₀≃g₁ from L to L′, fixed P, n,m∈ℤ with m=n−1 and
z∈Hom(P,L)^n, the (n,m) component of the postcomposition homotopy is z≫h. In source degree i
this is z_i≫h_{i+n}:P_i→L′_{i+n−1}. -/
@[simp]
theorem linearPostHomotopyCochain_v (P : CochainComplex C ℤ)
    {L L' : CochainComplex C ℤ} {g₀ g₁ : L ⟶ L'} (h : Homotopy g₀ g₁)
    (n m : ℤ) (hnm : n + (-1) = m) (z : Cochain P L n) :
    (linearPostHomotopyCochain R P h).v n m hnm z =
      z.comp (Cochain.ofHomotopy h) hnm := rfl

/-- Let R be a ring in universe uR and C a preadditive R-linear category with independent object
universe uC and morphism universe vC. For h:g₀≃g₁ between integer cochain maps L→L′ and fixed P,
let H(z)=z≫h be the induced degree-minus-one Hom-complex cochain. Then δH=H(id_P,g₀)−H(id_P,g₁)
as degree-zero cochains between Hom(P,L) and Hom(P,L′). The signed Hom Leibniz identity gives
this exact difference. -/
theorem linearPostHomotopyCochain_delta (P : CochainComplex C ℤ)
    {L L' : CochainComplex C ℤ} {g₀ g₁ : L ⟶ L'} (h : Homotopy g₀ g₁) :
    δ (-1) 0 (linearPostHomotopyCochain R P h) =
      Cochain.ofHom (linearComplexMap R (𝟙 P) g₀) -
        Cochain.ofHom (linearComplexMap R (𝟙 P) g₁) := by
  apply Cochain.ext₀
  intro n
  rw [δ_v (-1) 0 (by decide) _ n n (add_zero n) (n - 1) (n + 1) rfl rfl]
  simp only [Int.negOnePow_zero, one_smul, Cochain.sub_v, Cochain.ofHom_v]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change δ (n - 1) n (z.comp (Cochain.ofHomotopy h) (by omega)) +
      (δ n (n + 1) z).comp (Cochain.ofHomotopy h) (by omega) =
    mapLinearOver R (𝟙 P) g₀ n z - mapLinearOver R (𝟙 P) g₁ n z
  rw [δ_comp z (Cochain.ofHomotopy h) (show n + (-1) = n - 1 by omega)
    (n + 1) 0 n (by omega) rfl (by decide)]
  simp only [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul]
  rw [δ_ofHomotopy, Cochain.comp_sub, mapLinearOver_post, mapLinearOver_post]
  abel

/-- Let R be a ring in universe uR and C a preadditive R-linear category with independent object
universe uC and morphism universe vC. For h:g₀≃g₁ between maps L→L′ and fixed integer cochain
complex P, the induced R-linear maps H(id_P,g₀),H(id_P,g₁):Hom(P,L)→Hom(P,L′) are homotopic. The
homotopy's degree-n component is the operator z↦z≫h into degree n−1. -/
def linearComplexMapPostHomotopy (P : CochainComplex C ℤ)
    {L L' : CochainComplex C ℤ} {g₀ g₁ : L ⟶ L'} (h : Homotopy g₀ g₁) :
    Homotopy (linearComplexMap R (𝟙 P) g₀) (linearComplexMap R (𝟙 P) g₁) :=
  (Cochain.equivHomotopy _ _).symm
    ⟨linearPostHomotopyCochain R P h, by
      rw [linearPostHomotopyCochain_delta, sub_add_cancel]⟩

/-- Let R be a ring in universe uR and C a preadditive R-linear category with independent object
universe uC and morphism universe vC. For a source homotopy h:f₀≃f₁ between maps P′→P and fixed
integer cochain complex L, this degree-minus-one Hom-complex cochain sends z∈Hom(P,L)^n to
(-1)^n times h composed with z. Its component in source degree i is (-1)^n•(h_i≫z_{i-1}), valued
in L_{i+n−1}. -/
def linearPreHomotopyCochain {P P' : CochainComplex C ℤ}
    {f₀ f₁ : P' ⟶ P} (h : Homotopy f₀ f₁) (L : CochainComplex C ℤ) :
    Cochain (linearComplex R P L) (linearComplex R P' L) (-1) :=
  Cochain.mk fun n m hnm => ModuleCat.ofHom
    { toFun := fun z => n.negOnePow • (Cochain.ofHomotopy h).comp z (by omega)
      map_add' z z' := by
        simp only [Cochain.comp_add, smul_add]
      map_smul' r z := by
        simp only [Cochain.comp_smul, smul_comm n.negOnePow r, RingHom.id_apply] }

/-- Let R be a ring in universe uR and C a preadditive R-linear category with independent object
universe uC and morphism universe vC. For h:f₀≃f₁ from P′ to P, fixed L and n,m∈ℤ with m=n−1,
the component on z∈Hom(P,L)^n is (-1)^n•(h≫z). In source degree i it is
(-1)^n•(h_i≫z_{i-1}):P′_i→L_{i+n−1}. -/
@[simp]
theorem linearPreHomotopyCochain_v {P P' : CochainComplex C ℤ}
    {f₀ f₁ : P' ⟶ P} (h : Homotopy f₀ f₁) (L : CochainComplex C ℤ)
    (n m : ℤ) (hnm : n + (-1) = m) (z : Cochain P L n) :
    (linearPreHomotopyCochain R h L).v n m hnm z =
      n.negOnePow • (Cochain.ofHomotopy h).comp z (by omega) := rfl

/-- Let R be a ring in universe uR and C a preadditive R-linear category with independent object
universe uC and morphism universe vC. For h:f₀≃f₁ between maps P′→P and fixed integer cochain
complex L, let H_n(z)=(-1)^n•(h≫z). Then δH=H(f₀,id_L)−H(f₁,id_L) as degree-zero cochains
Hom(P,L)→Hom(P′,L). The successive signs (-1)^n and (-1)^{n+1} cancel the mixed differential
terms. -/
theorem linearPreHomotopyCochain_delta {P P' : CochainComplex C ℤ}
    {f₀ f₁ : P' ⟶ P} (h : Homotopy f₀ f₁) (L : CochainComplex C ℤ) :
    δ (-1) 0 (linearPreHomotopyCochain R h L) =
      Cochain.ofHom (linearComplexMap R f₀ (𝟙 L)) -
        Cochain.ofHom (linearComplexMap R f₁ (𝟙 L)) := by
  apply Cochain.ext₀
  intro n
  rw [δ_v (-1) 0 (by decide) _ n n (add_zero n) (n - 1) (n + 1) rfl rfl]
  simp only [Int.negOnePow_zero, one_smul, Cochain.sub_v, Cochain.ofHom_v]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change δ (n - 1) n (n.negOnePow •
      (Cochain.ofHomotopy h).comp z (by omega)) +
      (n + 1).negOnePow • (Cochain.ofHomotopy h).comp (δ n (n + 1) z) (by omega) =
    mapLinearOver R f₀ (𝟙 L) n z - mapLinearOver R f₁ (𝟙 L) n z
  rw [δ_units_smul,
    δ_comp (Cochain.ofHomotopy h) z (show (-1) + n = n - 1 by omega)
      0 (n + 1) n (by omega) (by decide) rfl,
    Int.negOnePow_succ, smul_add, smul_smul, Int.units_mul_self, one_smul,
    Units.neg_smul, δ_ofHomotopy, Cochain.sub_comp,
    mapLinearOver_pre, mapLinearOver_pre]
  abel

/-- Let R be a ring in universe uR and C a preadditive R-linear category with independent object
universe uC and morphism universe vC. For h:f₀≃f₁ between maps P′→P and fixed integer cochain
complex L, the maps H(f₀,id_L),H(f₁,id_L):Hom(P,L)→Hom(P′,L) are homotopic. The homotopy sends a
degree-n cochain z to (-1)^n•(h≫z) in degree n−1. -/
def linearComplexMapPreHomotopy {P P' : CochainComplex C ℤ}
    {f₀ f₁ : P' ⟶ P} (h : Homotopy f₀ f₁) (L : CochainComplex C ℤ) :
    Homotopy (linearComplexMap R f₀ (𝟙 L)) (linearComplexMap R f₁ (𝟙 L)) :=
  (Cochain.equivHomotopy _ _).symm
    ⟨linearPreHomotopyCochain R h L, by
      rw [linearPreHomotopyCochain_delta, sub_add_cancel]⟩

end CochainComplex.HomComplex
