/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Embedding.PositiveNat
public import MathlibExt.Algebra.Homology.Embedding.StupidTruncInclusion

/-!
# Direct inclusion of the whole positive part

Only a category with zero morphisms and a zero object is needed. The
components are the existing native stupid-truncation coordinate maps.
The boundary from original degree one to zero is the only extra chain-map
condition; original degree zero is unrestricted. No homology or abelian
structure, tensor structure, or caller-supplied comparison isomorphism is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
universe v u

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

local notation "e₊" => ComplexShape.positiveNatEmbedding

variable (K : ChainComplex C ℕ)

/-- Include the original positive coordinates directly, using the actual zero boundary. -/
def positiveStupidTruncInclusion (hK : K.d 1 0 = 0) : K.stupidTrunc e₊ ⟶ K :=
  ChainComplex.ofHom (fun i => stupidTruncι.f K e₊ i) (by
    intro n
    cases n with
    | zero =>
        change stupidTruncι.f K e₊ 1 ≫ K.d 1 0 =
          (K.stupidTrunc e₊).d 1 0 ≫ stupidTruncι.f K e₊ 0
        rw [hK, comp_zero,
          stupidTruncι.f_eq_zero K e₊ 0 (by intro i; change i + 1 ≠ 0; omega),
          comp_zero]
    | succ n =>
        rw [stupidTruncι.f_eq K e₊ (i := n + 1) (i' := n + 1 + 1) rfl,
          stupidTruncι.f_eq K e₊ (i := n) (i' := n + 1) rfl,
          stupidTrunc_d_eq K e₊ (i := n + 1) (j := n)
            (i' := n + 1 + 1) (j' := n + 1) rfl rfl]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- Every retained component is the whole original positive-degree coordinate map. -/
@[reassoc]
theorem positiveStupidTruncInclusion_f
    (hK : K.d 1 0 = 0) {i i' : ℕ} (hi : i + 1 = i') :
    (K.positiveStupidTruncInclusion hK).f i' = (K.stupidTruncXIso e₊ hi).hom :=
  stupidTruncι.f_eq K e₊ hi

/-- The strict source is zero in degree zero; the original target object is unrestricted. -/
@[simp]
theorem positiveStupidTruncInclusion_f_zero (hK : K.d 1 0 = 0) :
    (K.positiveStupidTruncInclusion hK).f 0 = 0 :=
  stupidTruncι.f_eq_zero K e₊ 0 (by intro i; change i + 1 ≠ 0; omega)

/-- The actual inclusion is monic without any abelian or homology hypothesis. -/
theorem mono_positiveStupidTruncInclusion (hK : K.d 1 0 = 0) :
    Mono (K.positiveStupidTruncInclusion hK) := by
  apply HomologicalComplex.mono_of_mono_f
  intro i
  cases i with
  | zero =>
      exact (K.isZero_stupidTrunc_X e₊ 0 (by intro j; change j + 1 ≠ 0; omega)).mono _
  | succ i =>
      rw [positiveStupidTruncInclusion_f K hK (i := i) rfl]
      infer_instance

variable {K} {L : ChainComplex C ℕ}

/-- Original chain maps commute with the direct strict inclusions under the two boundary laws. -/
@[reassoc]
theorem positiveStupidTruncInclusion_naturality
    (φ : K ⟶ L) (hK : K.d 1 0 = 0) (hL : L.d 1 0 = 0) :
    stupidTruncMap φ e₊ ≫ L.positiveStupidTruncInclusion hL =
      K.positiveStupidTruncInclusion hK ≫ φ := by
  ext i'
  by_cases hi' : ∃ i, e₊.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simpa only [comp_f, positiveStupidTruncInclusion_f K hK hi,
      positiveStupidTruncInclusion_f L hL hi] using
      stupidTruncMap_stupidTruncXIso_hom φ e₊ hi
  · exact (K.isZero_stupidTrunc_X e₊ i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src _ _

end HomologicalComplex
