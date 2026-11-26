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

public import MathlibExt.Algebra.Homology.ChainGradedPairingPositiveQuotient
public import MathlibExt.Algebra.Homology.ChainGradedPairingStrictPositive
public import Mathlib.Algebra.Category.ModuleCat.Kernels

/-!
# Both-positive images and the cokernel of a chain pairing

In an abelian monoidal category with additive tensoring, a chain pairing
whose two degree-one-to-zero differentials vanish restricts to
K₁,≥1⊗K₂,≥1→K₃. Its strict-positive cokernel is functorial in maps
of the original pairing diagrams.

In a module category with chosen monoidal preadditive tensor, the
component range is J_n=∑_(p,q>0,p+q=n)range(P_(p,q)).
The pointwise quotient K₃,n/J_n has the chain-cokernel universal property,
with descents annihilating the strict-positive pairing.
Its comparison with the categorical cokernel preserves projections
and pairing-square maps. Both source bidegrees are positive.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v

namespace HomologicalComplex.ChainGradedPairing


section GeneralCokernels

variable {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  {K₁ K₂ K₃ : ChainComplex C ℕ}
  (P : ChainGradedPairing K₁ K₂ K₃)
  (h₁ : K₁.d 1 0 = 0) (h₂ : K₂.d 1 0 = 0)

local notation "e₊" => ComplexShape.positiveNatEmbedding

section Naturality

variable {L₁ L₂ L₃ : ChainComplex C ℕ}
  (Q : ChainGradedPairing L₁ L₂ L₃)
  (g₁ : L₁.d 1 0 = 0) (g₂ : L₂.d 1 0 = 0)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
  (hf : tensorHom f₁ f₂ ≫ Q = P ≫ f₃)

include hf

/-- Let C be an abelian monoidal category with additive tensoring.
Let P:K₁⊗K₂→K₃ be a graded pairing of nonnegative chain complexes
with K₁.d(1,0)=K₂.d(1,0)=0.
Write P₊₊:K₁,≥1⊗K₂,≥1→K₃ for the strict-positive map.
Let Q be a second pairing with both first differentials zero and
f_i:K_i→L_i chain maps satisfying f₃∘P=Q∘(f₁⊗f₂).
The positive truncation maps of f₁,f₂ make the restricted
pairing square commute:
f₃∘P₊₊=Q₊₊∘(f₁,≥1⊗f₂,≥1). -/
@[reassoc]
theorem strictPositivePairing_naturality :
    tensorHom (stupidTruncMap f₁ e₊) (stupidTruncMap f₂ e₊) ≫
        strictPositivePairing Q g₁ g₂ =
      strictPositivePairing P h₁ h₂ ≫ f₃ := by
  calc
    _ = tensorHom (K₁.positiveStupidTruncInclusion h₁)
          (K₂.positiveStupidTruncInclusion h₂) ≫ (tensorHom f₁ f₂ ≫ Q) := by
      rw [strictPositivePairing, ← Category.assoc, tensorHom_comp_tensorHom,
        positiveStupidTruncInclusion_naturality, positiveStupidTruncInclusion_naturality,
        ← tensorHom_comp_tensorHom, Category.assoc]
    _ = tensorHom (K₁.positiveStupidTruncInclusion h₁)
          (K₂.positiveStupidTruncInclusion h₂) ≫ (P ≫ f₃) := by rw [hf]
    _ = _ := by simp only [strictPositivePairing, Category.assoc]

/-- Let C be an abelian monoidal category with additive tensoring.
Let P:K₁⊗K₂→K₃ be a graded pairing of nonnegative chain complexes
with K₁.d(1,0)=K₂.d(1,0)=0.
Write P₊₊:K₁,≥1⊗K₂,≥1→K₃ for the strict-positive map.
Let Q be a second pairing with both first differentials zero and
f_i:K_i→L_i chain maps satisfying f₃∘P=Q∘(f₁⊗f₂).
The original pairing square induces the cokernel map
Coker(P₊₊)→Coker(Q₊₊). -/
def strictPositiveCokernelMap :
    strictPositiveCokernel P h₁ h₂ ⟶ strictPositiveCokernel Q g₁ g₂ :=
  cokernel.map (strictPositivePairing P h₁ h₂) (strictPositivePairing Q g₁ g₂)
    (tensorHom (stupidTruncMap f₁ e₊) (stupidTruncMap f₂ e₊)) f₃
    (strictPositivePairing_naturality P h₁ h₂ Q g₁ g₂ f₁ f₂ f₃ hf).symm

/-- Let C be an abelian monoidal category with additive tensoring.
Let P:K₁⊗K₂→K₃ be a graded pairing of nonnegative chain complexes
with K₁.d(1,0)=K₂.d(1,0)=0.
Write P₊₊:K₁,≥1⊗K₂,≥1→K₃ for the strict-positive map.
Let Q be a second pairing with both first differentials zero and
f_i:K_i→L_i chain maps satisfying f₃∘P=Q∘(f₁⊗f₂).
The strict-positive projections satisfy
cokerMap∘π_P=π_Q∘f₃. -/
@[reassoc]
theorem strictPositiveProjection_map :
    strictPositiveProjection P h₁ h₂ ≫
        strictPositiveCokernelMap P h₁ h₂ Q g₁ g₂ f₁ f₂ f₃ hf =
      f₃ ≫ strictPositiveProjection Q g₁ g₂ :=
  cokernel.π_desc _ _ _

end Naturality

include h₁ h₂

/-- Let C be an abelian monoidal category with additive tensoring.
Let P:K₁⊗K₂→K₃ be a graded pairing of nonnegative chain complexes
with K₁.d(1,0)=K₂.d(1,0)=0.
Write P₊₊:K₁,≥1⊗K₂,≥1→K₃ for the strict-positive map.
The cokernel map induced by the identity pairing diagram
is the identity of Coker(P₊₊). -/
@[simp]
theorem strictPositiveCokernelMap_id :
    strictPositiveCokernelMap P h₁ h₂ P h₁ h₂ (𝟙 K₁) (𝟙 K₂) (𝟙 K₃)
      (by simp only [tensorHom_id_id, Category.id_comp, Category.comp_id]) =
        𝟙 (strictPositiveCokernel P h₁ h₂) := by
  let hπ : Epi (strictPositiveProjection P h₁ h₂) :=
    inferInstanceAs (Epi (cokernel.π (strictPositivePairing P h₁ h₂)))
  apply (cancel_epi (strictPositiveProjection P h₁ h₂)).1
  rw [strictPositiveProjection_map, Category.id_comp, Category.comp_id]

/-- Let C be an abelian monoidal category with additive tensoring.
Let P:K₁⊗K₂→K₃ be a graded pairing of nonnegative chain complexes
with K₁.d(1,0)=K₂.d(1,0)=0.
Write P₊₊:K₁,≥1⊗K₂,≥1→K₃ for the strict-positive map.
For two composable original pairing diagrams, each with the
two first differentials zero, the induced strict-positive cokernel
maps compose to the cokernel map of the composite diagram. -/
@[reassoc]
theorem strictPositiveCokernelMap_comp
    {L₁ L₂ L₃ M₁ M₂ M₃ : ChainComplex C ℕ}
    (Q : ChainGradedPairing L₁ L₂ L₃) (S : ChainGradedPairing M₁ M₂ M₃)
    (g₁ : L₁.d 1 0 = 0) (g₂ : L₂.d 1 0 = 0)
    (s₁ : M₁.d 1 0 = 0) (s₂ : M₂.d 1 0 = 0)
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
    (k₁ : L₁ ⟶ M₁) (k₂ : L₂ ⟶ M₂) (k₃ : L₃ ⟶ M₃)
    (hf : tensorHom f₁ f₂ ≫ Q = P ≫ f₃)
    (hk : tensorHom k₁ k₂ ≫ S = Q ≫ k₃) :
    strictPositiveCokernelMap P h₁ h₂ Q g₁ g₂ f₁ f₂ f₃ hf ≫
        strictPositiveCokernelMap Q g₁ g₂ S s₁ s₂ k₁ k₂ k₃ hk =
      strictPositiveCokernelMap P h₁ h₂ S s₁ s₂ (f₁ ≫ k₁) (f₂ ≫ k₂) (f₃ ≫ k₃)
        (by rw [← tensorHom_comp_tensorHom, Category.assoc, hk,
          ← Category.assoc, hf, Category.assoc]) := by
  let hπ : Epi (strictPositiveProjection P h₁ h₂) :=
    inferInstanceAs (Epi (cokernel.π (strictPositivePairing P h₁ h₂)))
  apply (cancel_epi (strictPositiveProjection P h₁ h₂)).1
  rw [← Category.assoc, strictPositiveProjection_map, Category.assoc,
    strictPositiveProjection_map, strictPositiveProjection_map, Category.assoc]

end GeneralCokernels

section ModuleImageQuotients

variable {R : Type u} [Ring R]
  [MonoidalCategory (ModuleCat.{v} R)] [MonoidalPreadditive (ModuleCat.{v} R)]
  {K₁ K₂ K₃ : ChainComplex (ModuleCat.{v} R) ℕ}
  (P : ChainGradedPairing K₁ K₂ K₃)
  (h₁ : K₁.d 1 0 = 0) (h₂ : K₂.d 1 0 = 0)

local notation "e₊" => ComplexShape.positiveNatEmbedding

/-- Let R be a ring in universe u and ModuleCat_v R have a chosen
monoidal preadditive structure. Let P be a chain pairing with both
first differentials zero. Its strict-positive map P₊₊ has bidegrees
p,q>0, and J_n=∑_(p,q>0,p+q=n)range(P_(p,q)).
In any p,q with p+q=n, the strict-positive component equals
P_(p,q) after the two positive-truncation inclusions in those degrees. -/
@[reassoc]
theorem strictPositivePairing_pairAt (p q n : ℕ) (h : p + q = n) :
    pairAt (strictPositivePairing P h₁ h₂) p q n h =
      ((K₁.positiveStupidTruncInclusion h₁).f p ⊗ₘ
        (K₂.positiveStupidTruncInclusion h₂).f q) ≫ pairAt P p q n h := by
  subst n
  have hc := pair_naturality (strictPositivePairing P h₁ h₂) P
    (K₁.positiveStupidTruncInclusion h₁)
    (K₂.positiveStupidTruncInclusion h₂) (𝟙 K₃)
    (by simp only [strictPositivePairing, Category.comp_id]) p q
  simpa only [pairAt_rfl, id_f, Category.comp_id] using hc.symm

private theorem strictPositiveComponent_mem (p q n : ℕ) (h : p + q = n)
    (x : ↥((K₁.stupidTrunc e₊).X p ⊗ (K₂.stupidTrunc e₊).X q)) :
    (pairAt (strictPositivePairing P h₁ h₂) p q n h).hom x ∈
      positiveImages P n := by
  by_cases hp : p = 0
  · subst p
    rw [strictPositivePairing_pairAt, positiveStupidTruncInclusion_f_zero]
    simp
  · by_cases hq : q = 0
    · subst q
      rw [strictPositivePairing_pairAt, positiveStupidTruncInclusion_f_zero]
      simp
    · rw [strictPositivePairing_pairAt]
      change (pairAt P p q n h).hom
        (((K₁.positiveStupidTruncInclusion h₁).f p ⊗ₘ
          (K₂.positiveStupidTruncInclusion h₂).f q).hom x) ∈ _
      exact pairAt_mem_positiveImages P p q n h (Nat.pos_of_ne_zero hp)
        (Nat.pos_of_ne_zero hq) _

private def strictPositiveComponentFactor (n : ℕ) :
    (tensorObj (K₁.stupidTrunc e₊) (K₂.stupidTrunc e₊)).X n ⟶
      ModuleCat.of R (positiveImages P n) :=
  HomologicalComplex.mapBifunctorDesc (fun p q h =>
    ModuleCat.ofHom
      ((pairAt (strictPositivePairing P h₁ h₂) p q n h).hom.codRestrict
        (positiveImages P n) (strictPositiveComponent_mem P h₁ h₂ p q n h)))

private theorem strictPositiveComponentFactor_comp (n : ℕ) :
    strictPositiveComponentFactor P h₁ h₂ n ≫
        ModuleCat.ofHom (positiveImages P n).subtype =
      (strictPositivePairing P h₁ h₂).f n := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have hι : ιTensorObj (K₁.stupidTrunc e₊) (K₂.stupidTrunc e₊) p q n h ≫
      strictPositiveComponentFactor P h₁ h₂ n =
        ModuleCat.ofHom
          ((pairAt (strictPositivePairing P h₁ h₂) p q n h).hom.codRestrict
            (positiveImages P n) (strictPositiveComponent_mem P h₁ h₂ p q n h)) :=
    by
      unfold strictPositiveComponentFactor
      exact HomologicalComplex.ι_mapBifunctorDesc
        (K₁ := K₁.stupidTrunc e₊) (K₂ := K₂.stupidTrunc e₊)
        (F := MonoidalCategory.curriedTensor (ModuleCat.{v} R))
        (c := ComplexShape.down ℕ) (j := n)
        (fun p q h => ModuleCat.ofHom
          ((pairAt (strictPositivePairing P h₁ h₂) p q n h).hom.codRestrict
            (positiveImages P n) (strictPositiveComponent_mem P h₁ h₂ p q n h))) p q h
  calc
    _ = (ιTensorObj (K₁.stupidTrunc e₊) (K₂.stupidTrunc e₊) p q n h ≫
          strictPositiveComponentFactor P h₁ h₂ n) ≫
            ModuleCat.ofHom (positiveImages P n).subtype := by rw [Category.assoc]
    _ = _ := congrArg (fun f => f ≫ ModuleCat.ofHom (positiveImages P n).subtype) hι

/-- Let R be a ring in universe u and ModuleCat_v R have a chosen
monoidal preadditive structure. Let P be a chain pairing with both
first differentials zero. Its strict-positive map P₊₊ has bidegrees
p,q>0, and J_n=∑_(p,q>0,p+q=n)range(P_(p,q)).
For f:K₃→L with f∘P₊₊=0, the pointwise quotient
has the induced chain descent desc(f):Q_J→L. -/
def positiveImageQuotientDesc
    {L : ChainComplex (ModuleCat.{v} R) ℕ} (f : K₃ ⟶ L)
    (hf : strictPositivePairing P h₁ h₂ ≫ f = 0) :
    positiveImageQuotient P h₁ h₂ ⟶ L :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom
    ((positiveImages P n).liftQ (f.f n).hom (by
      rw [← range_strictPositivePairing P h₁ h₂ n]
      rintro y ⟨x, rfl⟩
      have hc : (strictPositivePairing P h₁ h₂).f n ≫ f.f n = 0 := by
        simpa only [comp_f, zero_f] using congrArg (fun k => k.f n) hf
      simpa using ConcreteCategory.congr_hom hc x))) (by
    intro n
    apply ModuleCat.hom_ext
    ext z
    refine Quotient.inductionOn' z ?_
    intro x
    simp only [positiveImageQuotient, ChainComplex.of_d]
    change (L.d (n + 1) n).hom ((f.f (n + 1)).hom x) =
      (f.f n).hom ((K₃.d (n + 1) n).hom x)
    exact ConcreteCategory.congr_hom (f.comm (n + 1) n) x)

/-- Let R be a ring in universe u and ModuleCat_v R have a chosen
monoidal preadditive structure. Let P be a chain pairing with both
first differentials zero. Its strict-positive map P₊₊ has bidegrees
p,q>0, and J_n=∑_(p,q>0,p+q=n)range(P_(p,q)).
The induced descent satisfies desc(f)∘π_J=f for
a chain map f annihilating P₊₊. -/
@[reassoc]
theorem positiveImageProjection_desc
    {L : ChainComplex (ModuleCat.{v} R) ℕ} (f : K₃ ⟶ L)
    (hf : strictPositivePairing P h₁ h₂ ≫ f = 0) :
    positiveImageProjection P h₁ h₂ ≫ positiveImageQuotientDesc P h₁ h₂ f hf = f := by
  ext n x
  rfl

/-- Let R be a ring in universe u and ModuleCat_v R have a chosen
monoidal preadditive structure. Let P be a chain pairing with both
first differentials zero. Its strict-positive map P₊₊ has bidegrees
p,q>0, and J_n=∑_(p,q>0,p+q=n)range(P_(p,q)).
Any chain map m:Q_J→L with m∘π_J=f equals desc(f),
when f∘P₊₊=0. -/
theorem positiveImageQuotientDesc_unique
    {L : ChainComplex (ModuleCat.{v} R) ℕ} (f : K₃ ⟶ L)
    (hf : strictPositivePairing P h₁ h₂ ≫ f = 0)
    (m : positiveImageQuotient P h₁ h₂ ⟶ L)
    (hm : positiveImageProjection P h₁ h₂ ≫ m = f) :
    m = positiveImageQuotientDesc P h₁ h₂ f hf := by
  ext n z
  refine Quotient.inductionOn' z ?_
  intro x
  change (m.f n).hom ((positiveImages P n).mkQ x) = (f.f n).hom x
  exact congrArg (fun k : K₃ ⟶ L => (k.f n).hom x) hm

/-- Let R be a ring in universe u and ModuleCat_v R have a chosen
monoidal preadditive structure. Let P be a chain pairing with both
first differentials zero. Its strict-positive map P₊₊ has bidegrees
p,q>0, and J_n=∑_(p,q>0,p+q=n)range(P_(p,q)).
The quotient Q_J with π_J is a cokernel cofork of
P₊₊:K₁,≥1⊗K₂,≥1→K₃. -/
def positiveImageCokernelCofork : CokernelCofork (strictPositivePairing P h₁ h₂) :=
  CokernelCofork.ofπ (positiveImageProjection P h₁ h₂)
    (strictPositivePairing_comp_positiveImageProjection P h₁ h₂)

/-- Let R be a ring in universe u and ModuleCat_v R have a chosen
monoidal preadditive structure. Let P be a chain pairing with both
first differentials zero. Its strict-positive map P₊₊ has bidegrees
p,q>0, and J_n=∑_(p,q>0,p+q=n)range(P_(p,q)).
The positive image quotient cofork is limiting as a colimit
cofork: every map annihilating P₊₊ factors uniquely through π_J. -/
def positiveImageCokernelIsColimit : IsColimit (positiveImageCokernelCofork P h₁ h₂) :=
  CokernelCofork.IsColimit.ofπ (positiveImageProjection P h₁ h₂)
    (strictPositivePairing_comp_positiveImageProjection P h₁ h₂)
    (fun {_} f hf => positiveImageQuotientDesc P h₁ h₂ f hf)
    (fun {_} f hf => positiveImageProjection_desc P h₁ h₂ f hf)
    (fun {_} f hf m hm => positiveImageQuotientDesc_unique P h₁ h₂ f hf m hm)

/-- Let R be a ring in universe u and ModuleCat_v R have a chosen
monoidal preadditive structure. Let P be a chain pairing with both
first differentials zero. Its strict-positive map P₊₊ has bidegrees
p,q>0, and J_n=∑_(p,q>0,p+q=n)range(P_(p,q)).
The forward comparison satisfies α∘π_coker=π_J. -/
@[reassoc]
theorem strictPositiveProjection_comp_iso_hom :
    strictPositiveProjection P h₁ h₂ ≫
        (strictPositiveCokernelIsoPositiveImageQuotient P h₁ h₂).hom =
      positiveImageProjection P h₁ h₂ := by
  exact strictPositiveProjection_isoPositiveImage_hom P h₁ h₂

/-- Let R be a ring in universe u and ModuleCat_v R have a chosen
monoidal preadditive structure. Let P be a chain pairing with both
first differentials zero. Its strict-positive map P₊₊ has bidegrees
p,q>0, and J_n=∑_(p,q>0,p+q=n)range(P_(p,q)).
The inverse comparison satisfies α⁻¹∘π_J=π_coker. -/
@[reassoc]
theorem positiveImageProjection_comp_iso_inv :
    positiveImageProjection P h₁ h₂ ≫
        (strictPositiveCokernelIsoPositiveImageQuotient P h₁ h₂).inv =
      strictPositiveProjection P h₁ h₂ := by
  exact positiveImageProjection_isoStrictPositive_inv P h₁ h₂

section Naturality

variable {L₁ L₂ L₃ : ChainComplex (ModuleCat.{v} R) ℕ}
  (Q : ChainGradedPairing L₁ L₂ L₃)
  (g₁ : L₁.d 1 0 = 0) (g₂ : L₂.d 1 0 = 0)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
  (hf : tensorHom f₁ f₂ ≫ Q = P ≫ f₃)

include hf

/-- Let R be a ring in universe u and ModuleCat_v R have a chosen
monoidal preadditive structure. Let P be a chain pairing with both
first differentials zero. Its strict-positive map P₊₊ has bidegrees
p,q>0, and J_n=∑_(p,q>0,p+q=n)range(P_(p,q)).
For a second pairing Q with both first differentials zero and
an original pairing square (f₁,f₂,f₃), the categorical/image
cokernel comparisons commute with their induced quotient maps. -/
@[reassoc]
theorem strictPositiveCokernelIso_naturality :
    strictPositiveCokernelMap P h₁ h₂ Q g₁ g₂ f₁ f₂ f₃ hf ≫
        (strictPositiveCokernelIsoPositiveImageQuotient Q g₁ g₂).hom =
      (strictPositiveCokernelIsoPositiveImageQuotient P h₁ h₂).hom ≫
        positiveImageQuotientMap P h₁ h₂ Q g₁ g₂ f₁ f₂ f₃ hf := by
  let hπ : Epi (strictPositiveProjection P h₁ h₂) :=
    inferInstanceAs (Epi (cokernel.π (strictPositivePairing P h₁ h₂)))
  apply (cancel_epi (strictPositiveProjection P h₁ h₂)).1
  calc
    _ = (f₃ ≫ strictPositiveProjection Q g₁ g₂) ≫
          (strictPositiveCokernelIsoPositiveImageQuotient Q g₁ g₂).hom := by
      rw [← Category.assoc, strictPositiveProjection_map]
    _ = f₃ ≫ positiveImageProjection Q g₁ g₂ := by
      rw [Category.assoc, strictPositiveProjection_comp_iso_hom]
    _ = positiveImageProjection P h₁ h₂ ≫
          positiveImageQuotientMap P h₁ h₂ Q g₁ g₂ f₁ f₂ f₃ hf :=
      (positiveImageProjection_map P h₁ h₂ Q g₁ g₂ f₁ f₂ f₃ hf).symm
    _ = _ := by rw [← Category.assoc, strictPositiveProjection_comp_iso_hom]

end Naturality


end ModuleImageQuotients

end HomologicalComplex.ChainGradedPairing
