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
# Inclusion of positive chain coordinates

For a nonnegative chain complex with d_1 : K_1→K_0 equal to zero,
stupid truncation to positive degrees has a canonical monic inclusion
into K. It uses the original coordinates in every positive degree and
the zero map at degree zero.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
universe v u

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

local notation "e₊" => ChainComplex.kernelTailEmbedding

variable (K : ChainComplex C ℕ)

/--
Let C have zero morphisms and a zero object, and let K be a nonnegative chain complex with K.d
1 0 = 0. Let e(n)=n+1 and K₊=K.stupidTrunc e, which retains the positive degrees and is zero
at degree zero. The original positive coordinate inclusions and the zero map at degree zero
assemble into a complex morphism ι₊:K₊→K. The vanishing of d₁ ensures compatibility at the
endpoint.
-/
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

/--
Let C have zero morphisms and a zero object, and let K be a nonnegative chain complex with K.d
1 0 = 0. Let e(n)=n+1 and K₊=K.stupidTrunc e, which retains the positive degrees and is zero
at degree zero. If i'=i+1, the component ι₊.f i' equals the forward coordinate isomorphism
K₊_{i'}≅K_{i'} supplied by stupidTruncXIso.
-/
@[reassoc]
theorem positiveStupidTruncInclusion_f
    (hK : K.d 1 0 = 0) {i i' : ℕ} (hi : i + 1 = i') :
    (K.positiveStupidTruncInclusion hK).f i' = (K.stupidTruncXIso e₊ hi).hom :=
  stupidTruncι.f_eq K e₊ hi

/--
Let C have zero morphisms and a zero object, and let K be a nonnegative chain complex with K.d
1 0 = 0. Let e(n)=n+1 and K₊=K.stupidTrunc e, which retains the positive degrees and is zero
at degree zero. The degree-zero component of ι₊:K₊→K is the zero morphism from the zero source
term to K₀. The target object K₀ is not required to be zero.
-/
@[simp]
theorem positiveStupidTruncInclusion_f_zero (hK : K.d 1 0 = 0) :
    (K.positiveStupidTruncInclusion hK).f 0 = 0 :=
  stupidTruncι.f_eq_zero K e₊ 0 (by intro i; change i + 1 ≠ 0; omega)

/--
Let C have zero morphisms and a zero object, and let K be a nonnegative chain complex with K.d
1 0 = 0. Let e(n)=n+1 and K₊=K.stupidTrunc e, which retains the positive degrees and is zero
at degree zero. The canonical inclusion ι₊:K₊→K is a monomorphism: its positive components are
isomorphisms and its degree-zero source is a zero object. No abelian-category or homology
hypothesis is needed.
-/
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

/--
Let C have zero morphisms and a zero object, let φ:K→L be a morphism of nonnegative chain
complexes, and assume K.d 1 0 = L.d 1 0 = 0. For the positive embedding e(n)=n+1,
stupidTruncMap(φ,e) ≫ ι₊(L) = ι₊(K) ≫ φ.
-/
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
