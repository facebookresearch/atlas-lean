/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainGradedPairingPositiveQuotient
public import MathlibExt.Algebra.Homology.LinearHomCochainComplex

/-!
# Linear cochains on a quotient by positive pairing images

Let R be a commutative ring and P : K₁ ⊗ K₂ → K₃ a chain pairing in its module category with
an additive monoidal structure. If the degree-one boundaries of K₁ and K₂ vanish, the sums S_n
of images of components with p, q > 0 and p + q = n form a subcomplex. Let Q_P = K₃/S be the
quotient.

For a coefficient module G, its linear Hom-cochains have degree-n module Hom_R((Q_P)_n, G) and
differential φ ↦ d_Q ≫ φ. Pullback to K₃ is injective in every degree; its image consists
precisely of maps annihilating all positive pairing components. These cochains define
cohomology in every nonnegative degree, covariant in G and contravariant in compatible maps of
pairings.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped MonoidalCategory

universe u v

namespace HomologicalComplex.ChainGradedPairing

variable {R : Type u} [CommRing R]
  [MonoidalCategory (ModuleCat.{v} R)]
  [MonoidalPreadditive (ModuleCat.{v} R)]
  {K₁ K₂ K₃ : ChainComplex (ModuleCat.{v} R) ℕ}
  (P : ChainGradedPairing K₁ K₂ K₃)

/-- Let R be a commutative ring and equip ModuleCat.{v} R with a monoidal structure additive in
both variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a pairing of ℕ-indexed chain complexes. For n : ℕ, G :
ModuleCat.{v} R and φ : K₃.X n ⟶ G, one has positiveImages P n ≤ ker φ.hom if and only if
pairAt P p q n h ≫ φ = 0 for every p > 0, q > 0 and equality h : p + q = n. -/
theorem positiveImages_le_ker_iff (n : ℕ) {G : ModuleCat.{v} R}
    (φ : K₃.X n ⟶ G) :
    positiveImages P n ≤ LinearMap.ker φ.hom ↔
      ∀ (p q : ℕ) (h : p + q = n), 0 < p → 0 < q →
        pairAt P p q n h ≫ φ = 0 := by
  constructor
  · intro hφ p q h hp hq
    apply ModuleCat.hom_ext
    ext x
    change φ.hom ((pairAt P p q n h).hom x) = 0
    exact hφ (pairAt_mem_positiveImages P p q n h hp hq x)
  · intro hφ
    apply iSup_le
    intro z
    rintro y ⟨x, rfl⟩
    change φ.hom ((pairAt P z.1.1 z.1.2 n z.2.2.2).hom x) = 0
    exact ConcreteCategory.congr_hom
      (hφ z.1.1 z.1.2 z.2.2.2 z.2.1 z.2.2.1) x

variable (h₁ : K₁.d 1 0 = 0) (h₂ : K₂.d 1 0 = 0)

/-- Let R be a commutative ring and equip ModuleCat.{v} R with a monoidal structure additive in
both variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a pairing of ℕ-indexed chain complexes. Assume K₁.d 1
0 = K₂.d 1 0 = 0, and let Q_P be the chain quotient of K₃ by S_n = positiveImages P n in each
degree, with projection π_P : K₃ ⟶ Q_P. For G : ModuleCat.{v} R, define
positiveImageCochainComplex P h₁ h₂ G to be Hom_R(Q_P, G), a cochain complex indexed by ℕ. Its
degree-n module is Hom_R((Q_P)_n, G), and its differential is precomposition with the quotient
boundary. -/
def positiveImageCochainComplex (G : ModuleCat.{v} R) :
    CochainComplex (ModuleCat.{v} R) ℕ :=
  (linearHomCochainComplexFunctor R (ModuleCat.{v} R) G).obj
    (Opposite.op (positiveImageQuotient P h₁ h₂))

/-- Let R be a commutative ring and equip ModuleCat.{v} R with a monoidal structure additive in
both variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a pairing of ℕ-indexed chain complexes. Assume K₁.d 1
0 = K₂.d 1 0 = 0, and let Q_P be the chain quotient of K₃ by S_n = positiveImages P n in each
degree, with projection π_P : K₃ ⟶ Q_P. For G : ModuleCat.{v} R, n : ℕ, φ : (Q_P)_n ⟶ G and x
: (Q_P)_(n+1), the coboundary satisfies (δφ)(x) = φ(d_Q(n+1,n)(x)). This is the degree-n to n
+ 1 differential of the linear Hom-cochain complex. -/
theorem positiveImageCochainComplex_d_apply (G : ModuleCat.{v} R) (n : ℕ)
    (φ : (positiveImageQuotient P h₁ h₂).X n ⟶ G)
    (x : (positiveImageQuotient P h₁ h₂).X (n + 1)) :
    (((positiveImageCochainComplex P h₁ h₂ G).d n (n + 1)).hom φ).hom x =
      φ.hom (((positiveImageQuotient P h₁ h₂).d (n + 1) n).hom x) := rfl

/-- Let R be a commutative ring and equip ModuleCat.{v} R with a monoidal structure additive in
both variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a pairing of ℕ-indexed chain complexes. Assume K₁.d 1
0 = K₂.d 1 0 = 0, and let Q_P be the chain quotient of K₃ by S_n = positiveImages P n in each
degree, with projection π_P : K₃ ⟶ Q_P. For G : ModuleCat.{v} R, precomposition with π_P
defines a cochain map Hom_R(Q_P, G) ⟶ Hom_R(K₃, G), denoted positiveImageCochainInclusion. -/
def positiveImageCochainInclusion (G : ModuleCat.{v} R) :
    positiveImageCochainComplex P h₁ h₂ G ⟶
      (linearHomCochainComplexFunctor R (ModuleCat.{v} R) G).obj (Opposite.op K₃) :=
  (linearHomCochainComplexFunctor R (ModuleCat.{v} R) G).map
    (positiveImageProjection P h₁ h₂).op

/-- Let R be a commutative ring and equip ModuleCat.{v} R with a monoidal structure additive in
both variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a pairing of ℕ-indexed chain complexes. Assume K₁.d 1
0 = K₂.d 1 0 = 0, and let Q_P be the chain quotient of K₃ by S_n = positiveImages P n in each
degree, with projection π_P : K₃ ⟶ Q_P. For G : ModuleCat.{v} R, n : ℕ and φ : (Q_P)_n ⟶ G,
the degree-n value of positiveImageCochainInclusion is π_P.f n ≫ φ : K₃.X n ⟶ G. -/
theorem positiveImageCochainInclusion_f_apply (G : ModuleCat.{v} R) (n : ℕ)
    (φ : (positiveImageQuotient P h₁ h₂).X n ⟶ G) :
    ((positiveImageCochainInclusion P h₁ h₂ G).f n).hom φ =
      (positiveImageProjection P h₁ h₂).f n ≫ φ := rfl

/-- Let R be a commutative ring and equip ModuleCat.{v} R with a monoidal structure additive in
both variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a pairing of ℕ-indexed chain complexes. Assume K₁.d 1
0 = K₂.d 1 0 = 0, and let Q_P be the chain quotient of K₃ by S_n = positiveImages P n in each
degree, with projection π_P : K₃ ⟶ Q_P. For every G : ModuleCat.{v} R and n : ℕ, the degree-n
map Hom_R((Q_P)_n, G) → Hom_R(K₃.X n, G) given by precomposition with π_P.f n is injective. -/
theorem positiveImageCochainInclusion_f_injective (G : ModuleCat.{v} R) (n : ℕ) :
    Function.Injective ((positiveImageCochainInclusion P h₁ h₂ G).f n).hom := by
  intro φ ψ h
  apply ModuleCat.hom_ext
  ext z
  refine Quotient.inductionOn' z ?_
  intro x
  exact congrArg (fun τ : K₃.X n ⟶ G => τ.hom x) h

/-- Let R be a commutative ring and equip ModuleCat.{v} R with a monoidal structure additive in
both variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a pairing of ℕ-indexed chain complexes. Assume K₁.d 1
0 = K₂.d 1 0 = 0, and let Q_P be the chain quotient of K₃ by S_n = positiveImages P n in each
degree, with projection π_P : K₃ ⟶ Q_P. For n : ℕ, G : ModuleCat.{v} R and φ : K₃.X n ⟶ G,
there exists a unique ψ : (Q_P)_n ⟶ G with π_P.f n ≫ ψ = φ if and only if pairAt P p q n h ≫ φ
= 0 for every p > 0, q > 0 and h : p + q = n. -/
theorem existsUnique_positiveImageQuotient_cochain (n : ℕ) {G : ModuleCat.{v} R}
    (φ : K₃.X n ⟶ G) :
    (∃! ψ : (positiveImageQuotient P h₁ h₂).X n ⟶ G,
      (positiveImageProjection P h₁ h₂).f n ≫ ψ = φ) ↔
      ∀ (p q : ℕ) (h : p + q = n), 0 < p → 0 < q →
        pairAt P p q n h ≫ φ = 0 := by
  constructor
  · rintro ⟨ψ, hψ, _⟩ p q h hp hq
    rw [← hψ, ← Category.assoc, pairAt_comp_positiveImageProjection P h₁ h₂ p q n h hp hq,
      Limits.zero_comp]
  · intro hφ
    have hk : positiveImages P n ≤ LinearMap.ker φ.hom :=
      (positiveImages_le_ker_iff P n φ).2 hφ
    let ψ : (positiveImageQuotient P h₁ h₂).X n ⟶ G :=
      ModuleCat.ofHom ((positiveImages P n).liftQ φ.hom hk)
    refine ⟨ψ, ?_, ?_⟩
    · apply ModuleCat.hom_ext
      exact Submodule.liftQ_mkQ _ _ _
    · intro χ hχ
      apply ModuleCat.hom_ext
      ext z
      refine Quotient.inductionOn' z ?_
      intro x
      exact congrArg (fun τ : K₃.X n ⟶ G => τ.hom x) hχ

/-- Let R be a commutative ring and equip ModuleCat.{v} R with a monoidal structure additive in
both variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a pairing of ℕ-indexed chain complexes. Assume K₁.d 1
0 = K₂.d 1 0 = 0, and let Q_P be the chain quotient of K₃ by S_n = positiveImages P n in each
degree, with projection π_P : K₃ ⟶ Q_P. For G : ModuleCat.{v} R and every n : ℕ, define
positiveImageCohomology P h₁ h₂ G n as H^n(Hom_R(Q_P, G)), using the Hom-cochain differential
induced by the quotient boundary. -/
def positiveImageCohomology (G : ModuleCat.{v} R) (n : ℕ) : ModuleCat.{v} R :=
  (positiveImageCochainComplex P h₁ h₂ G).homology n

/-- Let R be a commutative ring and equip ModuleCat.{v} R with a monoidal structure additive in
both variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a pairing of ℕ-indexed chain complexes. Assume K₁.d 1
0 = K₂.d 1 0 = 0, and let Q_P be the chain quotient of K₃ by S_n = positiveImages P n in each
degree, with projection π_P : K₃ ⟶ Q_P. For each n : ℕ, the assignment G ↦ H^n(Hom_R(Q_P, G))
is a functor ModuleCat.{v} R ⥤ ModuleCat.{v} R. A coefficient morphism G ⟶ G' acts by
postcomposition on cochains and by its induced map on cohomology. -/
def positiveImageCohomologyFunctor (n : ℕ) : ModuleCat.{v} R ⥤ ModuleCat.{v} R :=
  linearHomCochainComplexHomologyFunctor R (ModuleCat.{v} R)
    (positiveImageQuotient P h₁ h₂) n

section Naturality

variable {L₁ L₂ L₃ : ChainComplex (ModuleCat.{v} R) ℕ}
  (Q : ChainGradedPairing L₁ L₂ L₃)
  (g₁ : L₁.d 1 0 = 0) (g₂ : L₂.d 1 0 = 0)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
  (hf : tensorHom f₁ f₂ ≫ Q = P ≫ f₃)

/-- Let R be a commutative ring and equip ModuleCat.{v} R with a monoidal structure additive in
both variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a pairing of ℕ-indexed chain complexes. Assume K₁.d 1
0 = K₂.d 1 0 = 0, and let Q_P be the chain quotient of K₃ by S_n = positiveImages P n in each
degree, with projection π_P : K₃ ⟶ Q_P. Let Q : L₁ ⊗ L₂ ⟶ L₃ be another pairing with L₁.d 1 0
= L₂.d 1 0 = 0. Let f_i : K_i ⟶ L_i satisfy tensorHom f₁ f₂ ≫ Q = P ≫ f₃, and write q(f) : Q_P
⟶ Q_Q for the induced quotient map. For G : ModuleCat.{v} R, precomposition with q(f) defines
positiveImageCochainMap : Hom_R(Q_Q, G) ⟶ Hom_R(Q_P, G). Its direction is contravariant in the
quotient chain map. -/
def positiveImageCochainMap (G : ModuleCat.{v} R) :
    positiveImageCochainComplex Q g₁ g₂ G ⟶ positiveImageCochainComplex P h₁ h₂ G :=
  (linearHomCochainComplexFunctor R (ModuleCat.{v} R) G).map
    (positiveImageQuotientMap P h₁ h₂ Q g₁ g₂ f₁ f₂ f₃ hf).op

/-- Let R be a commutative ring and equip ModuleCat.{v} R with a monoidal structure additive in
both variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a pairing of ℕ-indexed chain complexes. Assume K₁.d 1
0 = K₂.d 1 0 = 0, and let Q_P be the chain quotient of K₃ by S_n = positiveImages P n in each
degree, with projection π_P : K₃ ⟶ Q_P. Let Q : L₁ ⊗ L₂ ⟶ L₃ be another pairing with L₁.d 1 0
= L₂.d 1 0 = 0. Let f_i : K_i ⟶ L_i satisfy tensorHom f₁ f₂ ≫ Q = P ≫ f₃, and write q(f) : Q_P
⟶ Q_Q for the induced quotient map. For G : ModuleCat.{v} R, let I_P and I_Q be the cochain
maps induced by π_P and π_Q. Then Hom_R(q(f), G) ≫ I_P = I_Q ≫ Hom_R(f₃, G), as maps
Hom_R(Q_Q, G) ⟶ Hom_R(K₃, G). -/
@[reassoc]
theorem positiveImageCochainMap_inclusion (G : ModuleCat.{v} R) :
    positiveImageCochainMap P h₁ h₂ Q g₁ g₂ f₁ f₂ f₃ hf G ≫
        positiveImageCochainInclusion P h₁ h₂ G =
      positiveImageCochainInclusion Q g₁ g₂ G ≫
        (linearHomCochainComplexFunctor R (ModuleCat.{v} R) G).map f₃.op := by
  let F := linearHomCochainComplexFunctor R (ModuleCat.{v} R) G
  change F.map (positiveImageQuotientMap P h₁ h₂ Q g₁ g₂ f₁ f₂ f₃ hf).op ≫
      F.map (positiveImageProjection P h₁ h₂).op =
    F.map (positiveImageProjection Q g₁ g₂).op ≫ F.map f₃.op
  rw [← F.map_comp, ← F.map_comp]
  apply congrArg F.map
  exact congrArg Quiver.Hom.op
    (positiveImageProjection_map P h₁ h₂ Q g₁ g₂ f₁ f₂ f₃ hf)

/-- Let R be a commutative ring and equip ModuleCat.{v} R with a monoidal structure additive in
both variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a pairing of ℕ-indexed chain complexes. Assume K₁.d 1
0 = K₂.d 1 0 = 0, and let Q_P be the chain quotient of K₃ by S_n = positiveImages P n in each
degree, with projection π_P : K₃ ⟶ Q_P. Let Q : L₁ ⊗ L₂ ⟶ L₃ be another pairing with L₁.d 1 0
= L₂.d 1 0 = 0. Let f_i : K_i ⟶ L_i satisfy tensorHom f₁ f₂ ≫ Q = P ≫ f₃, and write q(f) : Q_P
⟶ Q_Q for the induced quotient map. For G : ModuleCat.{v} R and n : ℕ, the cochain pullback
along q(f) induces positiveImageCohomologyMap : H^n(Hom_R(Q_Q, G)) ⟶ H^n(Hom_R(Q_P, G)). -/
def positiveImageCohomologyMap (G : ModuleCat.{v} R) (n : ℕ) :
    positiveImageCohomology Q g₁ g₂ G n ⟶ positiveImageCohomology P h₁ h₂ G n :=
  HomologicalComplex.homologyMap
    (positiveImageCochainMap P h₁ h₂ Q g₁ g₂ f₁ f₂ f₃ hf G) n

end Naturality

end HomologicalComplex.ChainGradedPairing
