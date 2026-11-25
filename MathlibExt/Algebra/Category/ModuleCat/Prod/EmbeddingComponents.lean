/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.Prod.Components
public import MathlibExt.Algebra.Category.ModuleCat.Prod.Embeddings

/-!
# Embedding–component comparisons for `ModuleCat` over `R × S`

For a product ring `R × S` with idempotents `e = (1,0)` and `f = (0,1)`,
every `(R × S)`-module splits into its `e`- and `f`-submodules. This file
compares those components with the embeddings
`ModuleCat R ⥤ ModuleCat (R × S)` via `fst` and `ModuleCat S ⥤ ModuleCat (R × S)`
via `snd`: the `e`-component of an `fst`-embedded module is `⊤` and its
`f`-component is `⊥`, and symmetrically for `snd`. It provides the ambient
`(R × S)`-module identifications `eSubmodule ≃ embeddingFst.obj (eComponent)`
and `fSubmodule ≃ embeddingSnd.obj (fComponent)`, their functor and
natural-isomorphism versions, and the component-after-embedding isomorphisms
and zero-isomorphisms used downstream for decomposition and adjunctions.
-/

@[expose] public section

open CategoryTheory

universe v uR uS

namespace ProdIdempotent

section AmbientSmul

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable {M : Type*} [AddCommGroup M] [Module (R × S) M]

private lemma zero_snd_smul_of_mem_eSubmodule {m : M}
    (hm : m ∈ eSubmodule (R := R) (S := S) (M := M)) (s : S) :
    ((0 : R), s) • m = 0 := by
  have hf : f R S • m = 0 := f_smul_of_mem_eSubmodule_eq_zero hm
  have h_eq : ((0 : R), s) = ((0 : R), s) * f R S := by
    ext
    · simp [f]
    · simp [f]
  calc
    ((0 : R), s) • m = (((0 : R), s) * f R S) • m := by rw [← h_eq]
    _ = ((0 : R), s) • (f R S • m) := by rw [mul_smul]
    _ = ((0 : R), s) • (0 : M) := by rw [hf]
    _ = 0 := by rw [smul_zero]

private lemma zero_fst_smul_of_mem_fSubmodule {m : M}
    (hm : m ∈ fSubmodule (R := R) (S := S) (M := M)) (r : R) :
    (r, (0 : S)) • m = 0 := by
  have he : e R S • m = 0 := e_smul_of_mem_fSubmodule_eq_zero hm
  have h_eq : (r, (0 : S)) = (r, (0 : S)) * e R S := by
    ext
    · simp [e]
    · simp [e]
  calc
    (r, (0 : S)) • m = ((r, (0 : S)) * e R S) • m := by rw [← h_eq]
    _ = (r, (0 : S)) • (e R S • m) := by rw [mul_smul]
    _ = (r, (0 : S)) • (0 : M) := by rw [he]
    _ = 0 := by rw [smul_zero]

/-- For `m` in the `e`-submodule, `(R × S)`-action factors through `fst`. -/
lemma smul_eq_fst_smul_of_mem_eSubmodule {m : M}
    (hm : m ∈ eSubmodule (R := R) (S := S) (M := M)) (p : R × S) :
    p • m = (p.1, (0 : S)) • m := by
  have h_snd_zero := zero_snd_smul_of_mem_eSubmodule hm p.2
  have h_p_eq : p = (p.1, (0 : S)) + ((0 : R), p.2) := by
    ext
    · simp
    · simp
  calc
    p • m = ((p.1, (0 : S)) + ((0 : R), p.2)) • m := by rw [← h_p_eq]
    _ = (p.1, (0 : S)) • m + ((0 : R), p.2) • m := by rw [add_smul]
    _ = (p.1, (0 : S)) • m + 0 := by rw [h_snd_zero]
    _ = (p.1, (0 : S)) • m := by rw [add_zero]

/-- For `m` in the `f`-submodule, `(R × S)`-action factors through `snd`. -/
lemma smul_eq_snd_smul_of_mem_fSubmodule {m : M}
    (hm : m ∈ fSubmodule (R := R) (S := S) (M := M)) (p : R × S) :
    p • m = ((0 : R), p.2) • m := by
  have h_fst_zero := zero_fst_smul_of_mem_fSubmodule hm p.1
  have h_p_eq : p = (p.1, (0 : S)) + ((0 : R), p.2) := by
    ext
    · simp
    · simp
  calc
    p • m = ((p.1, (0 : S)) + ((0 : R), p.2)) • m := by rw [← h_p_eq]
    _ = (p.1, (0 : S)) • m + ((0 : R), p.2) • m := by rw [add_smul]
    _ = 0 + ((0 : R), p.2) • m := by rw [h_fst_zero]
    _ = ((0 : R), p.2) • m := by rw [zero_add]

end AmbientSmul

section EmbeddingsTopBot

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- `e`-submodule of an `R`-module embedded via `fst` is `⊤`. -/
lemma eSubmodule_prodEmbeddingFst_eq_top (N : ModuleCat.{v} R) :
    eSubmodule (R := R) (S := S) (M := (ModuleCat.prodEmbeddingFst R S).obj N) = ⊤ := by
  ext m
  simp only [Submodule.mem_top, iff_true]
  rw [mem_eSubmodule_iff]
  change ((1 : R), (0 : S)) • m = m
  have : ((1 : R), (0 : S)) • m = (1 : R) • (m : N) := rfl
  rw [this, one_smul]

private lemma fSubmodule_prodEmbeddingFst_eq_bot (N : ModuleCat.{v} R) :
    fSubmodule (R := R) (S := S) (M := (ModuleCat.prodEmbeddingFst R S).obj N) = ⊥ := by
  ext m
  constructor
  · intro hm
    rw [mem_fSubmodule_iff] at hm
    change ((0 : R), (1 : S)) • m = m at hm
    have h0 : (0 : R) • (m : N) = (m : N) := by
      have : ((0 : R), (1 : S)) • m = (0 : R) • (m : N) := rfl
      rw [this] at hm
      exact hm
    rw [Submodule.mem_bot]
    rw [zero_smul] at h0
    exact h0.symm
  · intro hm
    rw [Submodule.mem_bot] at hm
    rw [mem_fSubmodule_iff]
    change ((0 : R), (1 : S)) • (m : (ModuleCat.prodEmbeddingFst R S).obj N) = m
    rw [hm]
    change ((0 : R), (1 : S)) • (0 : (ModuleCat.prodEmbeddingFst R S).obj N) = 0
    rw [smul_zero]

/-- `f`-submodule of an `S`-module embedded via `snd` is `⊤`. -/
lemma fSubmodule_prodEmbeddingSnd_eq_top (P : ModuleCat.{v} S) :
    fSubmodule (R := R) (S := S) (M := (ModuleCat.prodEmbeddingSnd R S).obj P) = ⊤ := by
  ext m
  simp only [Submodule.mem_top, iff_true]
  rw [mem_fSubmodule_iff]
  change ((0 : R), (1 : S)) • m = m
  have : ((0 : R), (1 : S)) • m = (1 : S) • (m : P) := rfl
  rw [this, one_smul]

private lemma eSubmodule_prodEmbeddingSnd_eq_bot (P : ModuleCat.{v} S) :
    eSubmodule (R := R) (S := S) (M := (ModuleCat.prodEmbeddingSnd R S).obj P) = ⊥ := by
  ext m
  constructor
  · intro hm
    rw [mem_eSubmodule_iff] at hm
    have he_pair : e R S = ((1 : R), (0 : S)) := rfl
    rw [he_pair] at hm
    have h_pair : ((1 : R), (0 : S)) • m = (0 : S) • (m : P) := rfl
    rw [h_pair] at hm
    have h0 : (0 : S) • (m : P) = (m : P) := hm
    rw [Submodule.mem_bot]
    rw [zero_smul] at h0
    exact h0.symm
  · intro hm
    rw [Submodule.mem_bot] at hm
    rw [mem_eSubmodule_iff, hm]
    change e R S • (0 : (ModuleCat.prodEmbeddingSnd R S).obj P) = 0
    rw [smul_zero]

end EmbeddingsTopBot

section AmbientIso

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable (M : ModuleCat.{v} (R × S))

/-- The `(R × S)`-module structure on the `e`-component agrees with embedding
its `R`-module via `fst`. -/
noncomputable def eSubmoduleIsoEmbeddingFst :
    ModuleCat.of (R × S) (eSubmodule (R := R) (S := S) (M := M)) ≅
      (ModuleCat.prodEmbeddingFst R S).obj (eSubmoduleAsModuleCat (R := R) (S := S) M) := by
  let Eorig : ModuleCat.{v} (R × S) :=
    ModuleCat.of (R × S) (eSubmodule (R := R) (S := S) (M := M))
  let Eemb : ModuleCat.{v} (R × S) :=
    (ModuleCat.prodEmbeddingFst R S).obj (eSubmoduleAsModuleCat (R := R) (S := S) M)
  exact
    LinearEquiv.toModuleIso
      (@AddEquiv.toLinearEquiv _ _ _ _ _ _ Eorig.isModule Eemb.isModule (AddEquiv.refl _)
        (by
          intro p x
          apply Subtype.ext
          have hm : (x : M) ∈ eSubmodule (R := R) (S := S) (M := M) := x.2
          have h := smul_eq_fst_smul_of_mem_eSubmodule (R := R) (S := S) hm p
          exact h))

/-- The `(R × S)`-module structure on the `f`-component agrees with embedding
its `S`-module via `snd`. -/
noncomputable def fSubmoduleIsoEmbeddingSnd :
    ModuleCat.of (R × S) (fSubmodule (R := R) (S := S) (M := M)) ≅
      (ModuleCat.prodEmbeddingSnd R S).obj (fSubmoduleAsModuleCat (R := R) (S := S) M) := by
  let Forig : ModuleCat.{v} (R × S) :=
    ModuleCat.of (R × S) (fSubmodule (R := R) (S := S) (M := M))
  let Femb : ModuleCat.{v} (R × S) :=
    (ModuleCat.prodEmbeddingSnd R S).obj (fSubmoduleAsModuleCat (R := R) (S := S) M)
  exact
    LinearEquiv.toModuleIso
      (@AddEquiv.toLinearEquiv _ _ _ _ _ _ Forig.isModule Femb.isModule (AddEquiv.refl _)
        (by
          intro p x
          apply Subtype.ext
          have hm : (x : M) ∈ fSubmodule (R := R) (S := S) (M := M) := x.2
          have h := smul_eq_snd_smul_of_mem_fSubmodule (R := R) (S := S) hm p
          exact h))

end AmbientIso

section AmbientFunctor

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- Functor `ModuleCat (R×S) ⥤ ModuleCat (R×S)` sending `M` to its `e`-submodule
as an `(R×S)`-module. -/
def eSubmoduleFunctor : ModuleCat.{v} (R × S) ⥤ ModuleCat.{v} (R × S) where
  obj M := ModuleCat.of (R × S) (eSubmodule (R := R) (S := S) (M := M))
  map {X Y} f := ModuleCat.ofHom (map_eSubmodule (R := R) (S := S) f.hom)
  map_id X := by
    apply ModuleCat.hom_ext
    rfl
  map_comp {X Y Z} f g := by
    apply ModuleCat.hom_ext
    rfl

/-- Functor `ModuleCat (R×S) ⥤ ModuleCat (R×S)` sending `M` to its `f`-submodule. -/
def fSubmoduleFunctor : ModuleCat.{v} (R × S) ⥤ ModuleCat.{v} (R × S) where
  obj M := ModuleCat.of (R × S) (fSubmodule (R := R) (S := S) (M := M))
  map {X Y} f := ModuleCat.ofHom (map_fSubmodule (R := R) (S := S) f.hom)
  map_id X := by
    apply ModuleCat.hom_ext
    rfl
  map_comp {X Y Z} f g := by
    apply ModuleCat.hom_ext
    rfl

/-- Ambient identification of `e`-submodule functor with `eComponentFunctor ⋙ prodEmbeddingFst`. -/
noncomputable def eSubmoduleNatIsoEmbeddingFst :
    eSubmoduleFunctor (R := R) (S := S) ≅
      eComponentFunctor (R := R) (S := S) ⋙ ModuleCat.prodEmbeddingFst R S :=
  NatIso.ofComponents
    (fun M => eSubmoduleIsoEmbeddingFst M)
    (by
      intro X Y f
      apply ModuleCat.hom_ext
      rfl)

/-- Ambient identification of `f`-submodule functor with `fComponentFunctor ⋙ prodEmbeddingSnd`. -/
noncomputable def fSubmoduleNatIsoEmbeddingSnd :
    fSubmoduleFunctor (R := R) (S := S) ≅
      fComponentFunctor (R := R) (S := S) ⋙ ModuleCat.prodEmbeddingSnd R S :=
  NatIso.ofComponents
    (fun M => fSubmoduleIsoEmbeddingSnd M)
    (by
      intro X Y f
      apply ModuleCat.hom_ext
      rfl)

end AmbientFunctor

section EmbeddingComponentIso

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- The `e`-component of an `R`-module embedded via `fst` is that original module. -/
noncomputable def prodEmbeddingFst_eComponentIso (N : ModuleCat.{v} R) :
    eSubmoduleAsModuleCat (R := R) (S := S)
        ((ModuleCat.prodEmbeddingFst R S).obj N) ≅ N :=
  LinearEquiv.toModuleIso
    { toFun := fun x => x.val
      invFun := fun n =>
        ⟨n, by
          have : eSubmodule (R := R) (S := S)
              (M := (ModuleCat.prodEmbeddingFst R S).obj N) = ⊤ :=
            eSubmodule_prodEmbeddingFst_eq_top N
          rw [this]
          trivial⟩
      left_inv := by
        intro x
        apply Subtype.ext
        rfl
      right_inv := by
        intro n
        rfl
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro r x
        rfl }

private lemma prodEmbeddingFst_fComponent_subsingleton (N : ModuleCat.{v} R) :
    ∀ x y : fSubmoduleAsModuleCat
        (R := R) (S := S) ((ModuleCat.prodEmbeddingFst R S).obj N), x = y := by
  intro x y
  have hx : x.val = (0 : (ModuleCat.prodEmbeddingFst R S).obj N) := by
    have hm := x.2
    rw [mem_fSubmodule_iff] at hm
    change ((0 : R), (1 : S)) • (x.val) = x.val at hm
    have : ((0 : R), (1 : S)) • (x.val) = (0 : R) • (x.val) := rfl
    rw [this] at hm
    rw [zero_smul] at hm
    exact hm.symm
  have hy : y.val = (0 : (ModuleCat.prodEmbeddingFst R S).obj N) := by
    have hm := y.2
    rw [mem_fSubmodule_iff] at hm
    change ((0 : R), (1 : S)) • (y.val) = y.val at hm
    have : ((0 : R), (1 : S)) • (y.val) = (0 : R) • (y.val) := rfl
    rw [this] at hm
    rw [zero_smul] at hm
    exact hm.symm
  apply Subtype.ext
  rw [hx, hy]

/-- Explicit zero iso for `f`-component of `fst` embedding. -/
noncomputable def prodEmbeddingFst_fComponentZeroIso (N : ModuleCat.{v} R) :
    fSubmoduleAsModuleCat (R := R) (S := S)
        ((ModuleCat.prodEmbeddingFst R S).obj N) ≅ ModuleCat.of S PUnit :=
  LinearEquiv.toModuleIso
    { toFun := fun _ => PUnit.unit
      invFun := fun _ =>
        ⟨0, by
          show (0 : (ModuleCat.prodEmbeddingFst R S).obj N) ∈
            fSubmodule (R := R) (S := S) (M := (ModuleCat.prodEmbeddingFst R S).obj N)
          rw [mem_fSubmodule_iff]
          change ((0 : R), (1 : S)) • (0 : (ModuleCat.prodEmbeddingFst R S).obj N) = 0
          rw [smul_zero]⟩
      left_inv := by
        intro x
        have h := prodEmbeddingFst_fComponent_subsingleton (R := R) (S := S) N x
          ⟨0, by
            show (0 : (ModuleCat.prodEmbeddingFst R S).obj N) ∈
              fSubmodule (R := R) (S := S) (M := (ModuleCat.prodEmbeddingFst R S).obj N)
            rw [mem_fSubmodule_iff]
            change ((0 : R), (1 : S)) • (0 : (ModuleCat.prodEmbeddingFst R S).obj N) = 0
            rw [smul_zero]⟩
        exact h.symm
      right_inv := by
        intro _
        rfl
      map_add' := by
        intro _ _
        rfl
      map_smul' := by
        intro _ _
        rfl }

/-- The `f`-component of an `S`-module embedded via `snd` is that original module. -/
noncomputable def prodEmbeddingSnd_fComponentIso (P : ModuleCat.{v} S) :
    fSubmoduleAsModuleCat (R := R) (S := S)
        ((ModuleCat.prodEmbeddingSnd R S).obj P) ≅ P :=
  LinearEquiv.toModuleIso
    { toFun := fun x => x.val
      invFun := fun p =>
        ⟨p, by
          have : fSubmodule (R := R) (S := S)
              (M := (ModuleCat.prodEmbeddingSnd R S).obj P) = ⊤ :=
            fSubmodule_prodEmbeddingSnd_eq_top P
          rw [this]
          trivial⟩
      left_inv := by
        intro x
        apply Subtype.ext
        rfl
      right_inv := by
        intro p
        rfl
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro s x
        rfl }

private lemma prodEmbeddingSnd_eComponent_subsingleton (P : ModuleCat.{v} S) :
    ∀ x y : eSubmoduleAsModuleCat
        (R := R) (S := S) ((ModuleCat.prodEmbeddingSnd R S).obj P), x = y := by
  intro x y
  have hx : x.val = (0 : (ModuleCat.prodEmbeddingSnd R S).obj P) := by
    have hm := x.2
    rw [mem_eSubmodule_iff] at hm
    change ((1 : R), (0 : S)) • (x.val) = x.val at hm
    have : ((1 : R), (0 : S)) • (x.val) = (0 : S) • (x.val) := rfl
    rw [this] at hm
    rw [zero_smul] at hm
    exact hm.symm
  have hy : y.val = (0 : (ModuleCat.prodEmbeddingSnd R S).obj P) := by
    have hm := y.2
    rw [mem_eSubmodule_iff] at hm
    change ((1 : R), (0 : S)) • (y.val) = y.val at hm
    have : ((1 : R), (0 : S)) • (y.val) = (0 : S) • (y.val) := rfl
    rw [this] at hm
    rw [zero_smul] at hm
    exact hm.symm
  apply Subtype.ext
  rw [hx, hy]

/-- Explicit zero iso for `e`-component of `snd` embedding. -/
noncomputable def prodEmbeddingSnd_eComponentZeroIso (P : ModuleCat.{v} S) :
    eSubmoduleAsModuleCat (R := R) (S := S)
        ((ModuleCat.prodEmbeddingSnd R S).obj P) ≅ ModuleCat.of R PUnit :=
  LinearEquiv.toModuleIso
    { toFun := fun _ => PUnit.unit
      invFun := fun _ =>
        ⟨0, by
          show (0 : (ModuleCat.prodEmbeddingSnd R S).obj P) ∈
            eSubmodule (R := R) (S := S) (M := (ModuleCat.prodEmbeddingSnd R S).obj P)
          rw [mem_eSubmodule_iff]
          change ((1 : R), (0 : S)) • (0 : (ModuleCat.prodEmbeddingSnd R S).obj P) = 0
          rw [smul_zero]⟩
      left_inv := by
        intro x
        have h := prodEmbeddingSnd_eComponent_subsingleton (R := R) (S := S) P x
          ⟨0, by
            show (0 : (ModuleCat.prodEmbeddingSnd R S).obj P) ∈
              eSubmodule (R := R) (S := S) (M := (ModuleCat.prodEmbeddingSnd R S).obj P)
            rw [mem_eSubmodule_iff]
            change ((1 : R), (0 : S)) • (0 : (ModuleCat.prodEmbeddingSnd R S).obj P) = 0
            rw [smul_zero]⟩
        exact h.symm
      right_inv := by
        intro _
        rfl
      map_add' := by
        intro _ _
        rfl
      map_smul' := by
        intro _ _
        rfl }

section FunctorIso

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- Functor-level: `e`-component after `fst` embedding iso to identity. -/
noncomputable def eComponentEmbeddingFstNatIso :
    ModuleCat.prodEmbeddingFst (R := R) (S := S) ⋙
      eComponentFunctor (R := R) (S := S) ≅ 𝟭 (ModuleCat.{v} R) :=
  NatIso.ofComponents
    (fun N => prodEmbeddingFst_eComponentIso (R := R) (S := S) N)
    (by
      intro N N' f
      apply ModuleCat.hom_ext
      rfl)

/-- Functor-level: `f`-component after `snd` embedding iso to identity. -/
noncomputable def fComponentEmbeddingSndNatIso :
    ModuleCat.prodEmbeddingSnd (R := R) (S := S) ⋙
      fComponentFunctor (R := R) (S := S) ≅ 𝟭 (ModuleCat.{v} S) :=
  NatIso.ofComponents
    (fun P => prodEmbeddingSnd_fComponentIso (R := R) (S := S) P)
    (by
      intro P P' f
      apply ModuleCat.hom_ext
      rfl)

end FunctorIso

end EmbeddingComponentIso

end ProdIdempotent
