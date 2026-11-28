/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChainGradedPairingFirstPositiveImages
public import MathlibExt.Algebra.Homology.HomologicalComplexCokernelHomology
public import MathlibExt.Algebra.Homology.HomologicalComplexImageCokernel
public import MathlibExt.Algebra.Homology.HomologicalComplexModuleCokernel

/-!
# First-positive image quotient of a chain pairing

Let R be a ring and choose a monoidal preadditive structure on its module
category. For P:K₁⊗K₂→K₃ with K₁.d(1,0)=0, the first-positive map
P₊ uses K₁ in degrees ≥1 and every degree of K₂.
Its degree n image is I_n=∑_(p>0,q≥0,p+q=n)range(P_(p,q)).

The cokernel of the image inclusion is naturally the cokernel of P₊,
with degree coordinates K₃,n/I_n. Maps of the original pairings induce
the quotient maps, acting by f₃ on representative classes.
I₀=0, so the degree-zero projection and its induced H₀ map are
isomorphisms for the specified homology objects.
The ring and module carrier universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

universe u v

namespace HomologicalComplex.ChainGradedPairing

variable {R : Type u} [Ring R]
  [MonoidalCategory (ModuleCat.{v} R)] [MonoidalPreadditive (ModuleCat.{v} R)]
  {K₁ K₂ K₃ : ChainComplex (ModuleCat.{v} R) ℕ}
  (P : ChainGradedPairing K₁ K₂ K₃) (h₁ : K₁.d 1 0 = 0)

/-- Let R be a ring in universe u and choose a monoidal preadditive
structure on ModuleCat_v R. Let P:K₁⊗K₂→K₃ be a chain graded
pairing of nonnegative complexes, with K₁.d(1,0)=0.
Write P₊ for its first-positive map K₁,≥1⊗K₂→K₃ and
I_n=∑_(p>0,q≥0,p+q=n)range(P_(p,q)).
The first-positive image quotient is the chain cokernel of
image(P₊)→K₃. -/
def firstPositiveImageQuotient : ChainComplex (ModuleCat.{v} R) ℕ :=
  cokernel (Abelian.image.ι (firstPositivePairing P h₁))

/-- Let R be a ring in universe u and choose a monoidal preadditive
structure on ModuleCat_v R. Let P:K₁⊗K₂→K₃ be a chain graded
pairing of nonnegative complexes, with K₁.d(1,0)=0.
Write P₊ for its first-positive map K₁,≥1⊗K₂→K₃ and
I_n=∑_(p>0,q≥0,p+q=n)range(P_(p,q)).
The image quotient projection K₃→Q_I is the cokernel
projection of image(P₊)→K₃. -/
def firstPositiveImageProjection : K₃ ⟶ firstPositiveImageQuotient P h₁ :=
  cokernel.π (Abelian.image.ι (firstPositivePairing P h₁))

/-- Let R be a ring in universe u and choose a monoidal preadditive
structure on ModuleCat_v R. Let P:K₁⊗K₂→K₃ be a chain graded
pairing of nonnegative complexes, with K₁.d(1,0)=0.
Write P₊ for its first-positive map K₁,≥1⊗K₂→K₃ and
I_n=∑_(p>0,q≥0,p+q=n)range(P_(p,q)).
The canonical image/coimage comparison gives
Q_I≅Coker(P₊), with the same quotient representatives. -/
def firstPositiveImageQuotientIsoCokernel :
    firstPositiveImageQuotient P h₁ ≅ firstPositiveCokernel P h₁ :=
  Abelian.imageCokernelIso (firstPositivePairing P h₁)

/-- Let R be a ring in universe u and choose a monoidal preadditive
structure on ModuleCat_v R. Let P:K₁⊗K₂→K₃ be a chain graded
pairing of nonnegative complexes, with K₁.d(1,0)=0.
Write P₊ for its first-positive map K₁,≥1⊗K₂→K₃ and
I_n=∑_(p>0,q≥0,p+q=n)range(P_(p,q)).
For α:Q_I≅Coker(P₊), the projections satisfy
α∘π_I=π_coker. -/
@[reassoc (attr := simp)]
theorem firstPositiveImageProjection_comp_iso :
    firstPositiveImageProjection P h₁ ≫ (firstPositiveImageQuotientIsoCokernel P h₁).hom =
      firstPositiveProjection P h₁ :=
  Abelian.imageCokernelIso_projection (firstPositivePairing P h₁)

/-- Let R be a ring in universe u and choose a monoidal preadditive
structure on ModuleCat_v R. Let P:K₁⊗K₂→K₃ be a chain graded
pairing of nonnegative complexes, with K₁.d(1,0)=0.
Write P₊ for its first-positive map K₁,≥1⊗K₂→K₃ and
I_n=∑_(p>0,q≥0,p+q=n)range(P_(p,q)).
The inverse comparison obeys α⁻¹∘π_coker=π_I. -/
@[reassoc (attr := simp)]
theorem firstPositiveProjection_comp_imageIso_inv :
    firstPositiveProjection P h₁ ≫ (firstPositiveImageQuotientIsoCokernel P h₁).inv =
      firstPositiveImageProjection P h₁ :=
  Abelian.imageCokernelIso_projection_inv (firstPositivePairing P h₁)

/-- Let R be a ring in universe u and choose a monoidal preadditive
structure on ModuleCat_v R. Let P:K₁⊗K₂→K₃ be a chain graded
pairing of nonnegative complexes, with K₁.d(1,0)=0.
Write P₊ for its first-positive map K₁,≥1⊗K₂→K₃ and
I_n=∑_(p>0,q≥0,p+q=n)range(P_(p,q)).
The degree n image-quotient term is isomorphic to K₃,n/I_n,
using evaluation of the chain cokernel and the component image range. -/
def firstPositiveImageQuotientDegreeIso (n : ℕ) :
    (firstPositiveImageQuotient P h₁).X n ≅ firstPositiveDegreeQuotient P n :=
  moduleImageCokernelDegreeIso (firstPositivePairing P h₁) n ≪≫
    (Submodule.quotEquivOfEq _ _ (range_firstPositivePairing P h₁ n)).toModuleIso

/-- Let R be a ring in universe u and choose a monoidal preadditive
structure on ModuleCat_v R. Let P:K₁⊗K₂→K₃ be a chain graded
pairing of nonnegative complexes, with K₁.d(1,0)=0.
Write P₊ for its first-positive map K₁,≥1⊗K₂→K₃ and
I_n=∑_(p>0,q≥0,p+q=n)range(P_(p,q)).
The degree n quotient projection, followed by its degree
coordinate isomorphism, is x↦[x] in K₃,n/I_n. -/
@[reassoc]
theorem firstPositiveImageProjection_degreeIso (n : ℕ) :
    (firstPositiveImageProjection P h₁).f n ≫
        (firstPositiveImageQuotientDegreeIso P h₁ n).hom =
      ModuleCat.ofHom (firstPositiveImages P n).mkQ := by
  let π : K₃.X n ⟶ (cokernel (Abelian.image.ι (firstPositivePairing P h₁))).X n :=
    (cokernel.π (Abelian.image.ι (firstPositivePairing P h₁))).f n
  let e := moduleImageCokernelDegreeIso (firstPositivePairing P h₁) n
  let q := (Submodule.quotEquivOfEq _ _ (range_firstPositivePairing P h₁ n)).toModuleIso
  have hπ : π ≫ e.hom =
      ModuleCat.ofHom (LinearMap.range ((firstPositivePairing P h₁).f n).hom).mkQ :=
    moduleImageCokernelDegreeIso_projection (firstPositivePairing P h₁) n
  change π ≫ (e.hom ≫ q.hom) = _
  rw [← Category.assoc, hπ]
  apply ModuleCat.hom_ext
  ext x
  exact Submodule.quotEquivOfEq_mk _ _ (range_firstPositivePairing P h₁ n) x

/-- Let R be a ring in universe u and choose a monoidal preadditive
structure on ModuleCat_v R. Let P:K₁⊗K₂→K₃ be a chain graded
pairing of nonnegative complexes, with K₁.d(1,0)=0.
Write P₊ for its first-positive map K₁,≥1⊗K₂→K₃ and
I_n=∑_(p>0,q≥0,p+q=n)range(P_(p,q)).
For a chain map f:K₃→L, f∘P₊=0 exactly when f_n annihilates
I_n for every n and every element of that submodule. -/
theorem firstPositivePairing_comp_eq_zero_iff {L : ChainComplex (ModuleCat.{v} R) ℕ}
    (f : K₃ ⟶ L) :
    firstPositivePairing P h₁ ≫ f = 0 ↔
      ∀ n x, x ∈ firstPositiveImages P n → (f.f n).hom x = 0 := by
  constructor
  · intro hf n x hx
    rw [← range_firstPositivePairing P h₁ n] at hx
    obtain ⟨z, hz⟩ := hx
    have hc : (firstPositivePairing P h₁).f n ≫ f.f n = 0 := by
      simpa only [comp_f, zero_f] using congrArg (fun g => g.f n) hf
    rw [← hz]
    exact ConcreteCategory.congr_hom hc z
  · intro hf
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    ext x
    have hx : ((firstPositivePairing P h₁).f n).hom x ∈ firstPositiveImages P n := by
      rw [← range_firstPositivePairing P h₁ n]
      exact LinearMap.mem_range_self _ x
    exact hf n _ hx

/-- Let R be a ring in universe u and choose a monoidal preadditive
structure on ModuleCat_v R. Let P:K₁⊗K₂→K₃ be a chain graded
pairing of nonnegative complexes, with K₁.d(1,0)=0.
Write P₊ for its first-positive map K₁,≥1⊗K₂→K₃ and
I_n=∑_(p>0,q≥0,p+q=n)range(P_(p,q)).
A chain map f:K₃→L satisfying f∘P₊=0 factors through
the unique chain map Q_I→L induced by the image cokernel. -/
def firstPositiveImageQuotientDesc {L : ChainComplex (ModuleCat.{v} R) ℕ}
    (f : K₃ ⟶ L) (hf : firstPositivePairing P h₁ ≫ f = 0) :
    firstPositiveImageQuotient P h₁ ⟶ L :=
  Abelian.imageCokernelDesc (firstPositivePairing P h₁) f hf

/-- Let R be a ring in universe u and choose a monoidal preadditive
structure on ModuleCat_v R. Let P:K₁⊗K₂→K₃ be a chain graded
pairing of nonnegative complexes, with K₁.d(1,0)=0.
Write P₊ for its first-positive map K₁,≥1⊗K₂→K₃ and
I_n=∑_(p>0,q≥0,p+q=n)range(P_(p,q)).
The image-quotient descent desc(f) satisfies
desc(f)∘π_I=f for a chain map annihilating P₊. -/
@[reassoc (attr := simp)]
theorem firstPositiveImageProjection_desc {L : ChainComplex (ModuleCat.{v} R) ℕ}
    (f : K₃ ⟶ L) (hf : firstPositivePairing P h₁ ≫ f = 0) :
    firstPositiveImageProjection P h₁ ≫ firstPositiveImageQuotientDesc P h₁ f hf = f :=
  Abelian.imageCokernelDesc_projection (firstPositivePairing P h₁) f hf

/-- Let R be a ring in universe u and choose a monoidal preadditive
structure on ModuleCat_v R. Let P:K₁⊗K₂→K₃ be a chain graded
pairing of nonnegative complexes, with K₁.d(1,0)=0.
Write P₊ for its first-positive map K₁,≥1⊗K₂→K₃ and
I_n=∑_(p>0,q≥0,p+q=n)range(P_(p,q)).
For f annihilating P₊, any l:Q_I→L with l∘π_I=f
equals the image-cokernel descent of f. -/
theorem firstPositiveImageQuotientDesc_unique {L : ChainComplex (ModuleCat.{v} R) ℕ}
    (f : K₃ ⟶ L) (hf : firstPositivePairing P h₁ ≫ f = 0)
    (l : firstPositiveImageQuotient P h₁ ⟶ L)
    (hl : firstPositiveImageProjection P h₁ ≫ l = f) :
    l = firstPositiveImageQuotientDesc P h₁ f hf :=
  Abelian.imageCokernelDesc_unique (firstPositivePairing P h₁) f hf l hl

section Maps

variable {L₁ L₂ L₃ : ChainComplex (ModuleCat.{v} R) ℕ}
  (Q : ChainGradedPairing L₁ L₂ L₃) (g₁ : L₁.d 1 0 = 0)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
  (hf : tensorHom f₁ f₂ ≫ Q = P ≫ f₃)

include h₁ g₁ f₁ f₂ hf in
/-- For R a ring with a chosen monoidal preadditive module category,
let P,Q be chain pairings and f_i satisfy f₃∘P=Q∘(f₁⊗f₂).
Then f₃,n carries I_n(P), the sum of p>0,q≥0 ranges, into I_n(Q). -/
theorem firstPositiveImages_map (n : ℕ) :
    firstPositiveImages P n ≤ (firstPositiveImages Q n).comap (f₃.f n).hom := by
  intro x hx
  rw [← range_firstPositivePairing P h₁ n] at hx
  obtain ⟨z, hz⟩ := hx
  rw [← hz]
  rw [← range_firstPositivePairing Q g₁ n]
  have hc := congrArg (fun f => f.f n)
    (firstPositivePairing_naturality P h₁ Q g₁ f₁ f₂ f₃ hf)
  refine ⟨((tensorHom (stupidTruncMap f₁ ComplexShape.positiveNatEmbedding) f₂).f n).hom z, ?_⟩
  exact ConcreteCategory.congr_hom hc z

/-- Let R be a ring in universe u and choose a monoidal preadditive
structure on ModuleCat_v R. Let P:K₁⊗K₂→K₃ be a chain graded
pairing of nonnegative complexes, with K₁.d(1,0)=0.
Write P₊ for its first-positive map K₁,≥1⊗K₂→K₃ and
I_n=∑_(p>0,q≥0,p+q=n)range(P_(p,q)).
Let Q:L₁⊗L₂→L₃ have L₁.d(1,0)=0 and chain maps f_i:K_i→L_i
satisfy f₃∘P=Q∘(f₁⊗f₂).
The degree quotient map K₃,n/I_n(P)→L₃,n/I_n(Q) sends
[x] to [f₃,n(x)]. -/
def firstPositiveDegreeQuotientMap (n : ℕ) :
    firstPositiveDegreeQuotient P n ⟶ firstPositiveDegreeQuotient Q n :=
  ModuleCat.ofHom ((firstPositiveImages P n).mapQ (firstPositiveImages Q n)
    (f₃.f n).hom (firstPositiveImages_map P h₁ Q g₁ f₁ f₂ f₃ hf n))

/-- Let R be a ring in universe u and choose a monoidal preadditive
structure on ModuleCat_v R. Let P:K₁⊗K₂→K₃ be a chain graded
pairing of nonnegative complexes, with K₁.d(1,0)=0.
Write P₊ for its first-positive map K₁,≥1⊗K₂→K₃ and
I_n=∑_(p>0,q≥0,p+q=n)range(P_(p,q)).
Let Q:L₁⊗L₂→L₃ have L₁.d(1,0)=0 and chain maps f_i:K_i→L_i
satisfy f₃∘P=Q∘(f₁⊗f₂).
The representative quotient maps obey
q_Q∘f₃,n=quotMap_n∘q_P. -/
@[reassoc]
theorem firstPositiveDegreeQuotientMap_projection (n : ℕ) :
    ModuleCat.ofHom (firstPositiveImages P n).mkQ ≫
        firstPositiveDegreeQuotientMap P h₁ Q g₁ f₁ f₂ f₃ hf n =
      f₃.f n ≫ ModuleCat.ofHom (firstPositiveImages Q n).mkQ := by
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- Let R be a ring in universe u and choose a monoidal preadditive
structure on ModuleCat_v R. Let P:K₁⊗K₂→K₃ be a chain graded
pairing of nonnegative complexes, with K₁.d(1,0)=0.
Write P₊ for its first-positive map K₁,≥1⊗K₂→K₃ and
I_n=∑_(p>0,q≥0,p+q=n)range(P_(p,q)).
Let Q:L₁⊗L₂→L₃ have L₁.d(1,0)=0 and chain maps f_i:K_i→L_i
satisfy f₃∘P=Q∘(f₁⊗f₂).
The first-positive cokernel map and its degree-coordinate
isomorphisms commute with the representative map [x]↦[f₃,n(x)]. -/
@[reassoc]
theorem firstPositiveCokernelDegreeIso_naturality (n : ℕ) :
    (firstPositiveCokernelMap P h₁ Q g₁ f₁ f₂ f₃ hf).f n ≫
        (firstPositiveCokernelDegreeIso Q g₁ n).hom =
      (firstPositiveCokernelDegreeIso P h₁ n).hom ≫
        firstPositiveDegreeQuotientMap P h₁ Q g₁ f₁ f₂ f₃ hf n := by
  have hπ := congrArg (fun g => g.f n)
    (firstPositiveProjection_map P h₁ Q g₁ f₁ f₂ f₃ hf)
  have hcomponent : (firstPositiveProjection P h₁).f n ≫
      (firstPositiveCokernelMap P h₁ Q g₁ f₁ f₂ f₃ hf).f n =
      f₃.f n ≫ (firstPositiveProjection Q g₁).f n := by
    simpa only [HomologicalComplex.comp_f] using hπ
  letI : Epi ((firstPositiveProjection P h₁).f n) := by
    change Epi ((cokernel.π (firstPositivePairing P h₁)).f n)
    infer_instance
  apply (cancel_epi ((firstPositiveProjection P h₁).f n)).1
  rw [← Category.assoc, hcomponent, Category.assoc, firstPositiveProjection_degreeIso,
    ← Category.assoc, firstPositiveProjection_degreeIso]
  exact (firstPositiveDegreeQuotientMap_projection P h₁ Q g₁ f₁ f₂ f₃ hf n).symm

/-- Let R be a ring in universe u and choose a monoidal preadditive
structure on ModuleCat_v R. Let P:K₁⊗K₂→K₃ be a chain graded
pairing of nonnegative complexes, with K₁.d(1,0)=0.
Write P₊ for its first-positive map K₁,≥1⊗K₂→K₃ and
I_n=∑_(p>0,q≥0,p+q=n)range(P_(p,q)).
Let Q:L₁⊗L₂→L₃ have L₁.d(1,0)=0 and chain maps f_i:K_i→L_i
satisfy f₃∘P=Q∘(f₁⊗f₂).
The pairing square induces the chain map Q_I(P)→Q_I(Q)
on first-positive image quotients. -/
def firstPositiveImageQuotientMap :
    firstPositiveImageQuotient P h₁ ⟶ firstPositiveImageQuotient Q g₁ :=
  Abelian.imageCokernelMap (firstPositivePairing P h₁)
    (Arrow.homMk (tensorHom (stupidTruncMap f₁ ComplexShape.positiveNatEmbedding) f₂) f₃
      (firstPositivePairing_naturality P h₁ Q g₁ f₁ f₂ f₃ hf))

/-- Let R be a ring in universe u and choose a monoidal preadditive
structure on ModuleCat_v R. Let P:K₁⊗K₂→K₃ be a chain graded
pairing of nonnegative complexes, with K₁.d(1,0)=0.
Write P₊ for its first-positive map K₁,≥1⊗K₂→K₃ and
I_n=∑_(p>0,q≥0,p+q=n)range(P_(p,q)).
Let Q:L₁⊗L₂→L₃ have L₁.d(1,0)=0 and chain maps f_i:K_i→L_i
satisfy f₃∘P=Q∘(f₁⊗f₂).
The induced image quotient map satisfies
quotMap∘π_I,P=π_I,Q∘f₃. -/
@[reassoc (attr := simp)]
theorem firstPositiveImageProjection_map :
    firstPositiveImageProjection P h₁ ≫
        firstPositiveImageQuotientMap P h₁ Q g₁ f₁ f₂ f₃ hf =
      f₃ ≫ firstPositiveImageProjection Q g₁ :=
  Abelian.imageCokernelMap_projection (firstPositivePairing P h₁)
    (Arrow.homMk (tensorHom (stupidTruncMap f₁ ComplexShape.positiveNatEmbedding) f₂) f₃
      (firstPositivePairing_naturality P h₁ Q g₁ f₁ f₂ f₃ hf))

/-- Let R be a ring in universe u and choose a monoidal preadditive
structure on ModuleCat_v R. Let P:K₁⊗K₂→K₃ be a chain graded
pairing of nonnegative complexes, with K₁.d(1,0)=0.
Write P₊ for its first-positive map K₁,≥1⊗K₂→K₃ and
I_n=∑_(p>0,q≥0,p+q=n)range(P_(p,q)).
Let Q:L₁⊗L₂→L₃ have L₁.d(1,0)=0 and chain maps f_i:K_i→L_i
satisfy f₃∘P=Q∘(f₁⊗f₂).
The image/cokernel isomorphisms commute with the induced
chain quotient maps of P and Q. -/
@[reassoc]
theorem firstPositiveImageQuotientIsoCokernel_naturality :
    firstPositiveImageQuotientMap P h₁ Q g₁ f₁ f₂ f₃ hf ≫
        (firstPositiveImageQuotientIsoCokernel Q g₁).hom =
      (firstPositiveImageQuotientIsoCokernel P h₁).hom ≫
        firstPositiveCokernelMap P h₁ Q g₁ f₁ f₂ f₃ hf :=
  Abelian.imageCokernelIso_naturality (firstPositivePairing P h₁)
    (Arrow.homMk (tensorHom (stupidTruncMap f₁ ComplexShape.positiveNatEmbedding) f₂) f₃
      (firstPositivePairing_naturality P h₁ Q g₁ f₁ f₂ f₃ hf))

/-- Let R be a ring in universe u and choose a monoidal preadditive
structure on ModuleCat_v R. Let P:K₁⊗K₂→K₃ be a chain graded
pairing of nonnegative complexes, with K₁.d(1,0)=0.
Write P₊ for its first-positive map K₁,≥1⊗K₂→K₃ and
I_n=∑_(p>0,q≥0,p+q=n)range(P_(p,q)).
Let Q:L₁⊗L₂→L₃ have L₁.d(1,0)=0 and chain maps f_i:K_i→L_i
satisfy f₃∘P=Q∘(f₁⊗f₂).
The degree coordinate isomorphisms commute with the induced
image-quotient chain map and degree quotient representative maps. -/
@[reassoc]
theorem firstPositiveImageQuotientDegreeIso_naturality (n : ℕ) :
    (firstPositiveImageQuotientMap P h₁ Q g₁ f₁ f₂ f₃ hf).f n ≫
        (firstPositiveImageQuotientDegreeIso Q g₁ n).hom =
      (firstPositiveImageQuotientDegreeIso P h₁ n).hom ≫
        firstPositiveDegreeQuotientMap P h₁ Q g₁ f₁ f₂ f₃ hf n := by
  have hπ := congrArg (fun g => g.f n)
    (firstPositiveImageProjection_map P h₁ Q g₁ f₁ f₂ f₃ hf)
  have hcomponent : (firstPositiveImageProjection P h₁).f n ≫
      (firstPositiveImageQuotientMap P h₁ Q g₁ f₁ f₂ f₃ hf).f n =
      f₃.f n ≫ (firstPositiveImageProjection Q g₁).f n := by
    simpa only [HomologicalComplex.comp_f] using hπ
  letI : Epi ((firstPositiveImageProjection P h₁).f n) := by
    change Epi ((cokernel.π (Abelian.image.ι (firstPositivePairing P h₁))).f n)
    infer_instance
  apply (cancel_epi ((firstPositiveImageProjection P h₁).f n)).1
  rw [← Category.assoc, hcomponent, Category.assoc, firstPositiveImageProjection_degreeIso,
    ← Category.assoc, firstPositiveImageProjection_degreeIso]
  exact (firstPositiveDegreeQuotientMap_projection P h₁ Q g₁ f₁ f₂ f₃ hf n).symm

end Maps

/-- Let R be a ring in universe u and choose a monoidal preadditive
structure on ModuleCat_v R. Let P:K₁⊗K₂→K₃ be a chain graded
pairing of nonnegative complexes, with K₁.d(1,0)=0.
Write P₊ for its first-positive map K₁,≥1⊗K₂→K₃ and
I_n=∑_(p>0,q≥0,p+q=n)range(P_(p,q)).
The first-positive map has degree-zero component zero,
since no p>0,q≥0 satisfy p+q=0. -/
theorem firstPositivePairing_f_zero : (firstPositivePairing P h₁).f 0 = 0 := by
  apply ModuleCat.hom_ext
  ext x
  have hx : ((firstPositivePairing P h₁).f 0).hom x ∈ firstPositiveImages P 0 := by
    rw [← range_firstPositivePairing P h₁ 0]
    exact LinearMap.mem_range_self _ x
  simpa only [firstPositiveImages_zero, Submodule.mem_bot, ModuleCat.hom_zero,
    LinearMap.zero_apply] using hx

/-- Let R be a ring in universe u and choose a monoidal preadditive
structure on ModuleCat_v R. Let P:K₁⊗K₂→K₃ be a chain graded
pairing of nonnegative complexes, with K₁.d(1,0)=0.
Write P₊ for its first-positive map K₁,≥1⊗K₂→K₃ and
I_n=∑_(p>0,q≥0,p+q=n)range(P_(p,q)).
The degree-zero image quotient projection is an isomorphism
because I₀=0. -/
theorem firstPositiveImageProjection_f_zero_isIso :
    IsIso ((firstPositiveImageProjection P h₁).f 0) := by
  letI : IsIso ((firstPositiveProjection P h₁).f 0) :=
    isIso_cokernelProjection_f_of_zero (firstPositivePairing P h₁) 0
      (firstPositivePairing_f_zero P h₁)
  have h := congrArg (fun g => g.f 0) (firstPositiveProjection_comp_imageIso_inv P h₁)
  rw [← h]
  change IsIso ((firstPositiveProjection P h₁).f 0 ≫
    (firstPositiveImageQuotientIsoCokernel P h₁).inv.f 0)
  infer_instance

/-- Let R be a ring in universe u and choose a monoidal preadditive
structure on ModuleCat_v R. Let P:K₁⊗K₂→K₃ be a chain graded
pairing of nonnegative complexes, with K₁.d(1,0)=0.
Write P₊ for its first-positive map K₁,≥1⊗K₂→K₃ and
I_n=∑_(p>0,q≥0,p+q=n)range(P_(p,q)).
For the chosen degree-zero homology objects of K₃ and Q_I,
the image projection gives H₀(K₃)≅H₀(Q_I). -/
def firstPositiveImageHomologyZeroIso [K₃.HasHomology 0]
    [(firstPositiveImageQuotient P h₁).HasHomology 0] :
    K₃.homology 0 ≅ (firstPositiveImageQuotient P h₁).homology 0 :=
  cokernelHomologyZeroIso (firstPositivePairing P h₁) (firstPositivePairing_f_zero P h₁) ≪≫
    (imageCokernelHomologyIso (firstPositivePairing P h₁) 0).symm

/-- Let R be a ring in universe u and choose a monoidal preadditive
structure on ModuleCat_v R. Let P:K₁⊗K₂→K₃ be a chain graded
pairing of nonnegative complexes, with K₁.d(1,0)=0.
Write P₊ for its first-positive map K₁,≥1⊗K₂→K₃ and
I_n=∑_(p>0,q≥0,p+q=n)range(P_(p,q)).
The forward H₀ comparison for the chosen homology objects
is H₀(π_I), the homology map of the image quotient projection. -/
theorem firstPositiveImageHomologyZeroIso_hom [K₃.HasHomology 0]
    [(firstPositiveImageQuotient P h₁).HasHomology 0] :
    (firstPositiveImageHomologyZeroIso P h₁).hom =
      homologyMap (firstPositiveImageProjection P h₁) 0 := by
  apply (cancel_mono (imageCokernelHomologyIso (firstPositivePairing P h₁) 0).hom).1
  change (_ ≫ (imageCokernelHomologyIso (firstPositivePairing P h₁) 0).inv) ≫
      (imageCokernelHomologyIso (firstPositivePairing P h₁) 0).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (imageCokernelHomologyIso_projection (firstPositivePairing P h₁) 0).symm

end HomologicalComplex.ChainGradedPairing

end
