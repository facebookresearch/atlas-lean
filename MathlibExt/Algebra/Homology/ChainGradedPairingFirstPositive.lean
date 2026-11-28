/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainGradedPairingStrictPositive

/-!
# A pairing restricted to a positive first factor

Let `P : K₁ ⊗ K₂ ⟶ K₃` be a pairing of nonnegative chain complexes in an
abelian category with a preadditive monoidal structure. If `K₁.d 1 0 = 0`,
the positive stupid truncation of `K₁` includes as a subcomplex. Restricting
`P` along this inclusion retains the components with `p > 0`, `q ≥ 0` and
`p + q = n` in total degree `n`. Its cokernel quotients `K₃` by this image.
The second factor includes degree zero, unlike a both-positive restriction.
The construction is functorial in compatible morphisms of pairings.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

universe u v

namespace HomologicalComplex.ChainGradedPairing

variable {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  {K₁ K₂ K₃ : ChainComplex C ℕ} (P : ChainGradedPairing K₁ K₂ K₃)
  (h₁ : K₁.d 1 0 = 0)

local notation "e₊" => ChainComplex.kernelTailEmbedding

/-- For a pairing `P : K₁ ⊗ K₂ ⟶ K₃` with `K₁.d 1 0 = 0`, restrict its
first factor to the positive stupid truncation of `K₁` and retain all of `K₂`.
Thus the allowed bidegrees are `p > 0` and `q ≥ 0`, rather than both positive. -/
def firstPositivePairing : ChainGradedPairing (K₁.stupidTrunc e₊) K₂ K₃ :=
  tensorHom (K₁.positiveStupidTruncInclusion h₁) (𝟙 K₂) ≫ P

/-- In bidegree `(p, q)` with `p + q = n`, the first-positive pairing is the
original component of `P` preceded by the tensor product of the degree-`p`
positive-truncation inclusion and the identity on `K₂.X q`. -/
theorem firstPositivePairing_pairAt (p q n : ℕ) (h : p + q = n) :
    ιTensorObj (K₁.stupidTrunc e₊) K₂ p q n h ≫ (firstPositivePairing P h₁).f n =
      ((K₁.positiveStupidTruncInclusion h₁).f p ⊗ₘ (𝟙 K₂ : K₂ ⟶ K₂).f q) ≫
        (ιTensorObj K₁ K₂ p q n h ≫ P.f n) := by
  subst n
  have hc := pair_naturality (firstPositivePairing P h₁) P
    (K₁.positiveStupidTruncInclusion h₁) (𝟙 K₂) (𝟙 K₃)
    (by simp only [firstPositivePairing, Category.comp_id]) p q
  simpa only [pair, id_f, Category.comp_id] using hc.symm

/-- The cokernel chain complex of `P` restricted to its positive first factor,
assuming `K₁.d 1 0 = 0`. It quotients `K₃` by the image of all components
with `p > 0` and `q ≥ 0`; degree-zero second-factor components are included. -/
def firstPositiveCokernel : ChainComplex C ℕ := cokernel (firstPositivePairing P h₁)

/-- The canonical chain map from `K₃` to the cokernel of the first-positive
restriction of `P : K₁ ⊗ K₂ ⟶ K₃`, for `K₁.d 1 0 = 0`. Its composite
with the restricted pairing vanishes. -/
def firstPositiveProjection : K₃ ⟶ firstPositiveCokernel P h₁ :=
  cokernel.π (firstPositivePairing P h₁)

theorem firstPositivePairing_comp_projection :
    firstPositivePairing P h₁ ≫ firstPositiveProjection P h₁ = 0 := cokernel.condition _

section Maps

variable {L₁ L₂ L₃ : ChainComplex C ℕ} (Q : ChainGradedPairing L₁ L₂ L₃)
  (g₁ : L₁.d 1 0 = 0) (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
  (hf : tensorHom f₁ f₂ ≫ Q = P ≫ f₃)

include hf in
/-- Suppose the chain maps `(f₁, f₂, f₃)` preserve pairings `P` and `Q`, and
the first complexes of both pairings have zero differential from degree one
to zero. Their first-positive restrictions commute with the positive
truncation of `f₁`, the full map `f₂`, and the target map `f₃`. -/
theorem firstPositivePairing_naturality :
    tensorHom (stupidTruncMap f₁ e₊) f₂ ≫ firstPositivePairing Q g₁ =
      firstPositivePairing P h₁ ≫ f₃ := by
  have ht : tensorHom (stupidTruncMap f₁ e₊) f₂ ≫
        tensorHom (L₁.positiveStupidTruncInclusion g₁) (𝟙 L₂) =
      tensorHom (K₁.positiveStupidTruncInclusion h₁) (𝟙 K₂) ≫ tensorHom f₁ f₂ := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      positiveStupidTruncInclusion_naturality, Category.comp_id, Category.id_comp]
  calc
    _ = (tensorHom (stupidTruncMap f₁ e₊) f₂ ≫
        tensorHom (L₁.positiveStupidTruncInclusion g₁) (𝟙 L₂)) ≫ Q :=
      (Category.assoc _ _ _).symm
    _ = (tensorHom (K₁.positiveStupidTruncInclusion h₁) (𝟙 K₂) ≫ tensorHom f₁ f₂) ≫ Q :=
      congrArg (fun g => g ≫ Q) ht
    _ = tensorHom (K₁.positiveStupidTruncInclusion h₁) (𝟙 K₂) ≫
        (tensorHom f₁ f₂ ≫ Q) := Category.assoc _ _ _
    _ = tensorHom (K₁.positiveStupidTruncInclusion h₁) (𝟙 K₂) ≫ (P ≫ f₃) :=
      congrArg (fun g =>
      tensorHom (K₁.positiveStupidTruncInclusion h₁) (𝟙 K₂) ≫ g) hf
    _ = _ := (Category.assoc _ _ _).symm

/-- Compatible chain maps `(f₁, f₂, f₃)` between pairings `P` and `Q` induce
a chain map between their first-positive cokernels. Both first complexes
must have zero differential from degree one to zero; the induced map is
the cokernel map of the restricted pairing square. -/
def firstPositiveCokernelMap : firstPositiveCokernel P h₁ ⟶ firstPositiveCokernel Q g₁ :=
  cokernel.map (firstPositivePairing P h₁) (firstPositivePairing Q g₁)
    (tensorHom (stupidTruncMap f₁ e₊) f₂) f₃
    (firstPositivePairing_naturality P h₁ Q g₁ f₁ f₂ f₃ hf).symm

theorem firstPositiveProjection_map :
    firstPositiveProjection P h₁ ≫ firstPositiveCokernelMap P h₁ Q g₁ f₁ f₂ f₃ hf =
      f₃ ≫ firstPositiveProjection Q g₁ := cokernel.π_desc _ _ _

end Maps

/-- A chain map `f : K₃ ⟶ L` induces a map from the first-positive cokernel
of `P` to that of `P` followed by `f`. The latter cokernel quotients `L`
by the image under `f` of the first-positive pairing. -/
def firstPositiveCokernelPostcompMap {L : ChainComplex C ℕ} (f : K₃ ⟶ L) :
    firstPositiveCokernel P h₁ ⟶ firstPositiveCokernel (P.postcomp f) h₁ :=
  firstPositiveCokernelMap P h₁ (P.postcomp f) h₁ (𝟙 K₁) (𝟙 K₂) f
    (by simp only [tensorHom_id_id, Category.id_comp]; rfl)

/-- For a target chain map `f : K₃ ⟶ L`, projection to the first-positive
cokernel followed by the induced cokernel map equals `f` followed by
projection to the first-positive cokernel of `P` followed by `f`. -/
theorem firstPositiveProjection_postcompMap {L : ChainComplex C ℕ} (f : K₃ ⟶ L) :
    firstPositiveProjection P h₁ ≫ firstPositiveCokernelPostcompMap P h₁ f =
      f ≫ firstPositiveProjection (P.postcomp f) h₁ :=
  firstPositiveProjection_map P h₁ (P.postcomp f) h₁ (𝟙 K₁) (𝟙 K₂) f
    (by simp only [tensorHom_id_id, Category.id_comp]; rfl)

theorem firstPositiveCokernelMap_id :
    firstPositiveCokernelMap P h₁ P h₁ (𝟙 K₁) (𝟙 K₂) (𝟙 K₃)
      (by simp only [tensorHom_id_id, Category.id_comp, Category.comp_id]) =
        𝟙 (firstPositiveCokernel P h₁) := by
  exact cokernel.map_id (firstPositivePairing P h₁)
    (tensorHom (stupidTruncMap (𝟙 K₁) e₊) (𝟙 K₂))
    (firstPositivePairing_naturality P h₁ P h₁ (𝟙 K₁) (𝟙 K₂) (𝟙 K₃)
      (by simp only [tensorHom_id_id, Category.id_comp, Category.comp_id])).symm

include h₁ in
theorem firstPositiveCokernelMap_comp
    {L₁ L₂ L₃ T₁ T₂ T₃ : ChainComplex C ℕ}
    (Q : ChainGradedPairing L₁ L₂ L₃) (S : ChainGradedPairing T₁ T₂ T₃)
    (g₁ : L₁.d 1 0 = 0) (s₁ : T₁.d 1 0 = 0)
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
    (j₁ : L₁ ⟶ T₁) (j₂ : L₂ ⟶ T₂) (j₃ : L₃ ⟶ T₃)
    (hf : tensorHom f₁ f₂ ≫ Q = P ≫ f₃)
    (hj : tensorHom j₁ j₂ ≫ S = Q ≫ j₃) :
    firstPositiveCokernelMap P h₁ Q g₁ f₁ f₂ f₃ hf ≫
        firstPositiveCokernelMap Q g₁ S s₁ j₁ j₂ j₃ hj =
      firstPositiveCokernelMap P h₁ S s₁ (f₁ ≫ j₁) (f₂ ≫ j₂) (f₃ ≫ j₃)
        (by rw [← tensorHom_comp_tensorHom, Category.assoc, hj,
          ← Category.assoc, hf, Category.assoc]) := by
  apply (cancel_epi (cokernel.π (firstPositivePairing P h₁))).1
  change firstPositiveProjection P h₁ ≫
      (firstPositiveCokernelMap P h₁ Q g₁ f₁ f₂ f₃ hf ≫
        firstPositiveCokernelMap Q g₁ S s₁ j₁ j₂ j₃ hj) =
      firstPositiveProjection P h₁ ≫ _
  rw [← Category.assoc, firstPositiveProjection_map, Category.assoc,
    firstPositiveProjection_map, firstPositiveProjection_map, Category.assoc]

end HomologicalComplex.ChainGradedPairing
