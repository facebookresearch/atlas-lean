/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CategoryTheory_Functor_exists_corepresentableBy_of_faithfullyFlat_of_sheaf_univ.lean`
and
`P2M/Sol/S_CategoryTheory_Functor_exists_corepresentableBy_of_faithfullyFlat_of_sheaf_univ.lean`
and
`Theorems/Thm_CategoryTheory_Functor_exists_algEquiv_tensorProduct_descentDatum_of_corepresents_univ.lean`
and
`P2M/Sol/S_CategoryTheory_Functor_exists_algEquiv_tensorProduct_descentDatum_of_corepresents_univ.lean`
and
`Theorems/Thm_Module_FaithfullyFlat_exists_algebraMap_eq_of_tmul_one_eq_one_tmul.lean`
and
`P2M/Sol/S_Module_FaithfullyFlat_exists_algebraMap_eq_of_tmul_one_eq_one_tmul.lean`
and
`Theorems/Thm_CategoryTheory_Functor_exists_corepresentableBy_of_descentDatum_of_bijective_univ.lean`
and
`P2M/Sol/S_CategoryTheory_Functor_exists_corepresentableBy_of_descentDatum_of_bijective_univ.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import MathlibExt.RingTheory.Flat.FaithfullyFlat.AlgebraDescent

universe u v

open CategoryTheory CategoryTheory.Limits TensorProduct Algebra.TensorProduct


open CategoryTheory CategoryTheory.Limits TensorProduct Algebra.TensorProduct


namespace DatumFromFunctor

variable {R : Type u} [CommRing R] (F : Under (CommRingCat.of R) ⥤ Type v)
  (S₁ : Type u) [CommRing S₁] [Algebra R S₁]
  (C₁ : Type u) [CommRing C₁] [Algebra R C₁] [Algebra S₁ C₁] [IsScalarTower R S₁ C₁]

private abbrev ob (B : Type u) [CommRing B] [Algebra R B] : Under (CommRingCat.of R) :=
  Under.mk (CommRingCat.ofHom (algebraMap R B))

private abbrev hm {B B' : Type u} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] (ψ : B
    →ₐ[R] B') :
    ob (R := R) B ⟶ ob B' :=
  Under.homMk (CommRingCat.ofHom ψ.toRingHom) (by ext r; exact ψ.commutes r)

private theorem hm_comp {B B' B'' : Type u} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
    [CommRing B''] [Algebra R B'']
    (ψ : B →ₐ[R] B') (ψ' : B' →ₐ[R] B'') : hm (R := R) (ψ'.comp ψ) = hm ψ ≫ hm ψ' := by
  ext; rfl

private theorem map_comp_apply {B B' B'' : Type u} [CommRing B] [Algebra R B] [CommRing B']
    [Algebra R B'] [CommRing B'']
    [Algebra R B''] (ψ : B →ₐ[R] B') (ψ' : B' →ₐ[R] B'') (x : F.obj (ob B)) :
    F.map (hm (ψ'.comp ψ)) x = F.map (hm ψ') (F.map (hm ψ) x) := by
  rw [hm_comp, F.map_comp]; rfl

private theorem map_id_apply {B : Type u} [CommRing B] [Algebra R B] (x : F.obj (ob B)) :
    F.map (hm (AlgHom.id R B)) x = x := by
  have : hm (R := R) (AlgHom.id R B) = 𝟙 _ := by ext; rfl
  rw [this, F.map_id]; rfl

variable (e : ∀ (B : Type u) [CommRing B] [Algebra R B] (j : S₁ →ₐ[R] B),
      F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B))) ≃
        {g : C₁ →ₐ[R] B // g.comp (IsScalarTower.toAlgHom R S₁ C₁) = j})

private def Natural : Prop :=
  ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1

variable (he : Natural F S₁ C₁ e)

local notation "ι" => IsScalarTower.toAlgHom R S₁ C₁

include he in
private theorem nat {B B' : Type u} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
    (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (ob B)) (j' : S₁ →ₐ[R] B') (hj' : ψ.comp j = j') :
    ((e B' j') (F.map (hm ψ) x)).1 = ψ.comp ((e B j) x).1 := by
  subst hj'; exact he B B' j ψ x

private noncomputable def xu : F.obj (ob (R := R) C₁) := (e C₁ ι).symm ⟨AlgHom.id R C₁,
    AlgHom.id_comp _⟩

private theorem e_xu : ((e C₁ ι) (xu F S₁ C₁ e)).1 = AlgHom.id R C₁ := by
  simp [xu]

include he in
private theorem eq_map_xu {B : Type u} [CommRing B] [Algebra R B] (j : S₁ →ₐ[R] B) (x : F.obj
    (ob B)) :
    x = F.map (hm ((e B j x).1)) (xu F S₁ C₁ e) := by
  apply (e B j).injective
  apply Subtype.ext
  rw [nat F S₁ C₁ e he ι ((e B j x).1) (xu F S₁ C₁ e) j ((e B j x).2), e_xu, AlgHom.comp_id]

private noncomputable def x₀ : F.obj (ob (R := R) (S₁ ⊗[R] C₁)) :=
  F.map (hm (includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁)) (xu F S₁ C₁ e)

private noncomputable def g₀ : C₁ →ₐ[R] S₁ ⊗[R] C₁ :=
  ((e (S₁ ⊗[R] C₁) (includeLeft : S₁ →ₐ[R] S₁ ⊗[R] C₁)) (x₀ F S₁ C₁ e)).1

private theorem g₀_comp_ι : (g₀ F S₁ C₁ e).comp ι = includeLeft :=
  ((e (S₁ ⊗[R] C₁) (includeLeft : S₁ →ₐ[R] S₁ ⊗[R] C₁)) (x₀ F S₁ C₁ e)).2

include he in
private theorem e_x₀_right : ((e (S₁ ⊗[R] C₁) ((includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁).comp ι))
    (x₀ F S₁ C₁ e)).1 =
    includeRight := by
  have := nat F S₁ C₁ e he ι (includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁) (xu F S₁ C₁ e)
    ((includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁).comp ι) rfl
  rw [e_xu, AlgHom.comp_id] at this
  exact this

include he in
private theorem core {D : Type u} [CommRing D] [Algebra R D] (j₁ j₂ : S₁ →ₐ[R] D) (x : F.obj
    (ob D)) :
    ((e D j₁) x).1 = (Algebra.TensorProduct.lift j₁ ((e D j₂) x).1 (fun _ _ => Commute.all _
        _)).comp (g₀ F S₁ C₁ e) := by
  have hθR : (Algebra.TensorProduct.lift j₁ ((e D j₂) x).1 (fun _ _ => Commute.all _ _)).comp
      includeRight = ((e D j₂) x).1 :=
    Algebra.TensorProduct.lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _)
  have hθL : (Algebra.TensorProduct.lift j₁ ((e D j₂) x).1 (fun _ _ => Commute.all _ _)).comp
      includeLeft = j₁ :=
    Algebra.TensorProduct.lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _)
  have hx : F.map (hm (Algebra.TensorProduct.lift j₁ ((e D j₂) x).1 (fun _ _ => Commute.all _ _)))
      (x₀ F S₁ C₁ e) = x := by
    rw [x₀, ← map_comp_apply, hθR]
    exact (eq_map_xu F S₁ C₁ e he j₂ x).symm
  have key := nat F S₁ C₁ e he (B := S₁ ⊗[R] C₁) (B' := D) (includeLeft : S₁ →ₐ[R] S₁ ⊗[R] C₁)
    (Algebra.TensorProduct.lift j₁ ((e D j₂) x).1 (fun _ _ => Commute.all _ _)) (x₀ F S₁ C₁ e) j₁
        hθL
  rw [hx] at key
  rw [key, g₀]

private noncomputable def φ₀ : C₁ ⊗[R] S₁ →ₐ[R] S₁ ⊗[R] C₁ :=
  Algebra.TensorProduct.lift (g₀ F S₁ C₁ e) ((includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁).comp ι) (fun _
      _ => Commute.all _ _)

private theorem φ₀_tmul (c : C₁) (s : S₁) : φ₀ F S₁ C₁ e (c ⊗ₜ[R] s) = g₀ F S₁ C₁ e c * ((1 : S₁)
    ⊗ₜ[R] (ι s)) := by
  simp [φ₀, Algebra.TensorProduct.lift_tmul]

private theorem g₀_ι (s : S₁) : g₀ F S₁ C₁ e (ι s) = s ⊗ₜ[R] (1 : C₁) := by
  have := AlgHom.congr_fun (g₀_comp_ι F S₁ C₁ e) s
  simpa using this

include he in
private theorem intertwine {D : Type u} [CommRing D] [Algebra R D] (j₁ j₂ : S₁ →ₐ[R] D) (x : F.obj
    (ob D)) :
    Algebra.TensorProduct.lift ((e D j₁) x).1 j₂ (fun _ _ => Commute.all _ _) =
      (Algebra.TensorProduct.lift j₁ ((e D j₂) x).1 (fun _ _ => Commute.all _ _)).comp (φ₀ F S₁ C₁
          e) := by
  have hc := core F S₁ C₁ e he j₁ j₂ x
  have hg₂ι : ((e D j₂) x).1.comp ι = j₂ := ((e D j₂) x).2
  apply Algebra.TensorProduct.ext'
  intro c s
  rw [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, φ₀_tmul, map_mul,
      Algebra.TensorProduct.lift_tmul,
    map_one, one_mul]
  congr 1
  · exact AlgHom.congr_fun hc c
  · exact (AlgHom.congr_fun hg₂ι s).symm

private theorem φ₀_linear :
    (φ₀ F S₁ C₁ e).comp (Algebra.TensorProduct.map ι (AlgHom.id R S₁)) =
      Algebra.TensorProduct.map (AlgHom.id R S₁) ι := by
  apply Algebra.TensorProduct.ext'
  intro s s'
  rw [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, φ₀_tmul,
      g₀_ι]
  simp [Algebra.TensorProduct.tmul_mul_tmul]

private noncomputable def x₁ : F.obj (ob (R := R) (C₁ ⊗[R] S₁)) :=
  F.map (hm (includeLeft : C₁ →ₐ[R] C₁ ⊗[R] S₁)) (xu F S₁ C₁ e)

private noncomputable def h₀ : C₁ →ₐ[R] C₁ ⊗[R] S₁ :=
  ((e (C₁ ⊗[R] S₁) (includeRight : S₁ →ₐ[R] C₁ ⊗[R] S₁)) (x₁ F S₁ C₁ e)).1

private theorem h₀_comp_ι : (h₀ F S₁ C₁ e).comp ι = includeRight :=
  ((e (C₁ ⊗[R] S₁) (includeRight : S₁ →ₐ[R] C₁ ⊗[R] S₁)) (x₁ F S₁ C₁ e)).2

include he in
private theorem e_x₁_left : ((e (C₁ ⊗[R] S₁) ((includeLeft : C₁ →ₐ[R] C₁ ⊗[R] S₁).comp ι)) (x₁ F S₁
    C₁ e)).1 =
    includeLeft := by
  have := nat F S₁ C₁ e he ι (includeLeft : C₁ →ₐ[R] C₁ ⊗[R] S₁) (xu F S₁ C₁ e)
    ((includeLeft : C₁ →ₐ[R] C₁ ⊗[R] S₁).comp ι) rfl
  rw [e_xu, AlgHom.comp_id] at this
  exact this

include he in
private theorem core' {D : Type u} [CommRing D] [Algebra R D] (j₁ j₂ : S₁ →ₐ[R] D) (x : F.obj
    (ob D)) :
    ((e D j₂) x).1 = (Algebra.TensorProduct.lift ((e D j₁) x).1 j₂ (fun _ _ => Commute.all _
        _)).comp (h₀ F S₁ C₁ e) := by
  have hθL : (Algebra.TensorProduct.lift ((e D j₁) x).1 j₂ (fun _ _ => Commute.all _ _)).comp
      includeLeft = ((e D j₁) x).1 :=
    Algebra.TensorProduct.lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _)
  have hθR : (Algebra.TensorProduct.lift ((e D j₁) x).1 j₂ (fun _ _ => Commute.all _ _)).comp
      includeRight = j₂ :=
    Algebra.TensorProduct.lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _)
  have hx : F.map (hm (Algebra.TensorProduct.lift ((e D j₁) x).1 j₂ (fun _ _ => Commute.all _ _)))
      (x₁ F S₁ C₁ e) = x := by
    rw [x₁, ← map_comp_apply, hθL]
    exact (eq_map_xu F S₁ C₁ e he j₁ x).symm
  have key := nat F S₁ C₁ e he (B := C₁ ⊗[R] S₁) (B' := D) (includeRight : S₁ →ₐ[R] C₁ ⊗[R] S₁)
    (Algebra.TensorProduct.lift ((e D j₁) x).1 j₂ (fun _ _ => Commute.all _ _)) (x₁ F S₁ C₁ e) j₂
        hθR
  rw [hx] at key
  rw [key, h₀]

private noncomputable def ψ₀ : S₁ ⊗[R] C₁ →ₐ[R] C₁ ⊗[R] S₁ :=
  Algebra.TensorProduct.lift ((includeLeft : C₁ →ₐ[R] C₁ ⊗[R] S₁).comp ι) (h₀ F S₁ C₁ e) (fun _
      _ => Commute.all _ _)

private theorem ψ₀_tmul (s : S₁) (c : C₁) : ψ₀ F S₁ C₁ e (s ⊗ₜ[R] c) = ((ι s) ⊗ₜ[R] (1 : S₁)) * h₀
    F S₁ C₁ e c := by
  simp [ψ₀, Algebra.TensorProduct.lift_tmul]

include he in
private theorem intertwine' {D : Type u} [CommRing D] [Algebra R D] (j₁ j₂ : S₁ →ₐ[R] D) (x : F.obj
    (ob D)) :
    Algebra.TensorProduct.lift j₁ ((e D j₂) x).1 (fun _ _ => Commute.all _ _) =
      (Algebra.TensorProduct.lift ((e D j₁) x).1 j₂ (fun _ _ => Commute.all _ _)).comp (ψ₀ F S₁ C₁
          e) := by
  have hc := core' F S₁ C₁ e he j₁ j₂ x
  have hg₁ι : ((e D j₁) x).1.comp ι = j₁ := ((e D j₁) x).2
  apply Algebra.TensorProduct.ext'
  intro s c
  rw [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, ψ₀_tmul, map_mul,
      Algebra.TensorProduct.lift_tmul,
    map_one, mul_one]
  congr 1
  · exact (AlgHom.congr_fun hg₁ι s).symm
  · exact AlgHom.congr_fun hc c

include he in
private theorem ψ₀_comp_φ₀ : (ψ₀ F S₁ C₁ e).comp (φ₀ F S₁ C₁ e) = AlgHom.id R (C₁ ⊗[R] S₁) := by
  have h := intertwine F S₁ C₁ e he ((includeLeft : C₁ →ₐ[R] C₁ ⊗[R] S₁).comp ι) includeRight
      (x₁ F S₁ C₁ e)
  have h1 : ((e (C₁ ⊗[R] S₁) ((includeLeft : C₁ →ₐ[R] C₁ ⊗[R] S₁).comp ι)) (x₁ F S₁ C₁ e)).1
      = includeLeft :=
    e_x₁_left F S₁ C₁ e he
  rw [h1] at h
  rw [Algebra.TensorProduct.lift_includeLeft_includeRight] at h
  exact h.symm

include he in
private theorem φ₀_comp_ψ₀ : (φ₀ F S₁ C₁ e).comp (ψ₀ F S₁ C₁ e) = AlgHom.id R (S₁ ⊗[R] C₁) := by
  have h := intertwine' F S₁ C₁ e he includeLeft ((includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁).comp ι)
      (x₀ F S₁ C₁ e)
  have h2 : ((e (S₁ ⊗[R] C₁) ((includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁).comp ι)) (x₀ F S₁ C₁ e)).1
      = includeRight :=
    e_x₀_right F S₁ C₁ e he
  rw [h2] at h
  rw [Algebra.TensorProduct.lift_includeLeft_includeRight] at h
  exact h.symm

private noncomputable def φ (he : Natural F S₁ C₁ e) : C₁ ⊗[R] S₁ ≃ₐ[R] S₁ ⊗[R] C₁ :=
  AlgEquiv.ofAlgHom (φ₀ F S₁ C₁ e) (ψ₀ F S₁ C₁ e) (φ₀_comp_ψ₀ F S₁ C₁ e he) (ψ₀_comp_φ₀ F S₁ C₁ e
      he)

private theorem φ_toAlgHom (he : Natural F S₁ C₁ e) : (φ F S₁ C₁ e he).toAlgHom = φ₀ F S₁ C₁ e :=
    rfl

private theorem lift_includeLeft_includeRight_comp {Y : Type u} [CommRing Y] [Algebra R Y] (f : C₁
    →ₐ[R] Y) :
    Algebra.TensorProduct.lift (includeLeft : S₁ →ₐ[R] S₁ ⊗[R] Y) ((includeRight : Y →ₐ[R] S₁
        ⊗[R] Y).comp f)
      (fun _ _ => Commute.all _ _) = Algebra.TensorProduct.map (AlgHom.id R S₁) f := by
  apply Algebra.TensorProduct.ext'
  intro s c
  simp [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.tmul_mul_tmul]

include he in
private theorem coact (c : C₁) :
    Algebra.TensorProduct.map (AlgHom.id R S₁) (g₀ F S₁ C₁ e) (g₀ F S₁ C₁ e c) =
      Algebra.TensorProduct.map (AlgHom.id R S₁) (includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁) (g₀ F S₁ C₁ e
          c) := by
  let D₂ : Type u := S₁ ⊗[R] (S₁ ⊗[R] C₁)
  let inR₂ : S₁ ⊗[R] C₁ →ₐ[R] D₂ := includeRight
  let k₁ : S₁ →ₐ[R] D₂ := inR₂.comp (includeLeft : S₁ →ₐ[R] S₁ ⊗[R] C₁)
  let k₂ : S₁ →ₐ[R] D₂ := inR₂.comp ((includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁).comp ι)
  let k₀ : S₁ →ₐ[R] D₂ := includeLeft
  let x₂ : F.obj (ob D₂) := F.map (hm (B := S₁ ⊗[R] C₁) (B' := D₂) inR₂) (x₀ F S₁ C₁ e)
  have e1 : ((e D₂ k₁) x₂).1 = inR₂.comp (g₀ F S₁ C₁ e) :=
    nat F S₁ C₁ e he (B := S₁ ⊗[R] C₁) (B' := D₂) (includeLeft : S₁ →ₐ[R] S₁ ⊗[R] C₁) inR₂ (x₀ F S₁
        C₁ e) k₁ rfl
  have e2 : ((e D₂ k₂) x₂).1 = inR₂.comp includeRight := by
    have := nat F S₁ C₁ e he (B := S₁ ⊗[R] C₁) (B' := D₂) ((includeRight : C₁ →ₐ[R] S₁
        ⊗[R] C₁).comp ι) inR₂
      (x₀ F S₁ C₁ e) k₂ rfl
    rw [e_x₀_right F S₁ C₁ e he] at this
    exact this
  have c1 := core F S₁ C₁ e he (D := D₂) k₀ k₁ x₂
  have c2 := core F S₁ C₁ e he (D := D₂) k₀ k₂ x₂
  rw [e1, lift_includeLeft_includeRight_comp] at c1
  rw [e2, lift_includeLeft_includeRight_comp] at c2
  have := AlgHom.congr_fun (c1.symm.trans c2) c
  simpa only [AlgHom.comp_apply] using this

private theorem assoc_left (y : S₁ ⊗[R] C₁) :
    Algebra.TensorProduct.map (AlgHom.id R S₁) (φ₀ F S₁ C₁ e)
        ((Algebra.TensorProduct.assoc R R R S₁ C₁ S₁) (y ⊗ₜ[R] (1 : S₁))) =
      Algebra.TensorProduct.map (AlgHom.id R S₁) (g₀ F S₁ C₁ e) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.map_tmul, φ₀_tmul,
      map_one, AlgHom.id_apply, show ((1 : S₁) ⊗ₜ[R] (1 : C₁)) = (1 : S₁ ⊗[R] C₁) from rfl, mul_one]
  | add y₁ y₂ h₁ h₂ => simp only [add_tmul, map_add, h₁, h₂]

private theorem assoc_right (y : S₁ ⊗[R] C₁) :
    Algebra.TensorProduct.map (AlgHom.id R S₁) (Algebra.TensorProduct.comm R C₁ S₁).toAlgHom
        ((Algebra.TensorProduct.assoc R R R S₁ C₁ S₁) (y ⊗ₜ[R] (1 : S₁))) =
      Algebra.TensorProduct.map (AlgHom.id R S₁) (includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.map_tmul]
    simp [Algebra.TensorProduct.comm_tmul]
  | add y₁ y₂ h₁ h₂ => simp only [add_tmul, map_add, h₁, h₂]

include he in

private theorem cocycle :
    (Algebra.TensorProduct.map (AlgHom.id R S₁) (φ₀ F S₁ C₁ e)).comp
        ((Algebra.TensorProduct.assoc R R R S₁ C₁ S₁).toAlgHom.comp
          (Algebra.TensorProduct.map (φ₀ F S₁ C₁ e) (AlgHom.id R S₁))) =
      (Algebra.TensorProduct.map (AlgHom.id R S₁) (Algebra.TensorProduct.comm R C₁
          S₁).toAlgHom).comp
        ((Algebra.TensorProduct.assoc R R R S₁ C₁ S₁).toAlgHom.comp
          ((Algebra.TensorProduct.map (φ₀ F S₁ C₁ e) (AlgHom.id R S₁)).comp
            ((Algebra.TensorProduct.assoc R R R C₁ S₁ S₁).symm.toAlgHom.comp
              ((Algebra.TensorProduct.map (AlgHom.id R C₁) (Algebra.TensorProduct.comm R S₁
                  S₁).toAlgHom).comp
                (Algebra.TensorProduct.assoc R R R C₁ S₁ S₁).toAlgHom)))) := by
  apply Algebra.TensorProduct.ext'
  intro p s'
  induction p using TensorProduct.induction_on with
  | zero => simp
  | add p q hp hq => simp only [add_tmul, map_add, hp, hq]
  | tmul c s =>

    have L : (Algebra.TensorProduct.map (AlgHom.id R S₁) (φ₀ F S₁ C₁ e))
        ((Algebra.TensorProduct.assoc R R R S₁ C₁ S₁) ((φ₀ F S₁ C₁ e (c ⊗ₜ[R] s)) ⊗ₜ[R] s')) =
        Algebra.TensorProduct.map (AlgHom.id R S₁) (g₀ F S₁ C₁ e) (g₀ F S₁ C₁ e c) *
          ((1 : S₁) ⊗ₜ[R] (s ⊗ₜ[R] ι s')) := by
      rw [φ₀_tmul, show (g₀ F S₁ C₁ e c * ((1 : S₁) ⊗ₜ[R] ι s)) ⊗ₜ[R] s' =
        (g₀ F S₁ C₁ e c ⊗ₜ[R] (1 : S₁)) * ((((1 : S₁) ⊗ₜ[R] ι s)) ⊗ₜ[R] s') by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul], map_mul, map_mul, assoc_left,
        Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.map_tmul, φ₀_tmul, g₀_ι]
      simp [Algebra.TensorProduct.tmul_mul_tmul]

    have Rr : (Algebra.TensorProduct.map (AlgHom.id R S₁) (Algebra.TensorProduct.comm R C₁
        S₁).toAlgHom)
        ((Algebra.TensorProduct.assoc R R R S₁ C₁ S₁)
          ((Algebra.TensorProduct.map (φ₀ F S₁ C₁ e) (AlgHom.id R S₁))
            ((Algebra.TensorProduct.assoc R R R C₁ S₁ S₁).symm
              ((Algebra.TensorProduct.map (AlgHom.id R C₁) (Algebra.TensorProduct.comm R S₁
                  S₁).toAlgHom)
                ((Algebra.TensorProduct.assoc R R R C₁ S₁ S₁) ((c ⊗ₜ[R] s) ⊗ₜ[R] s')))))) =
        Algebra.TensorProduct.map (AlgHom.id R S₁) (includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁) (g₀ F S₁ C₁
            e c) *
          ((1 : S₁) ⊗ₜ[R] (s ⊗ₜ[R] ι s')) := by
      rw [Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.map_tmul, AlgEquiv.toAlgHom_apply,
        Algebra.TensorProduct.comm_tmul, AlgHom.id_apply, Algebra.TensorProduct.assoc_symm_tmul,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, φ₀_tmul,
        show (g₀ F S₁ C₁ e c * ((1 : S₁) ⊗ₜ[R] ι s')) ⊗ₜ[R] s =
          (g₀ F S₁ C₁ e c ⊗ₜ[R] (1 : S₁)) * ((((1 : S₁) ⊗ₜ[R] ι s')) ⊗ₜ[R] s) by
            rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul], map_mul, map_mul, assoc_right,
        Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.map_tmul]
      simp [Algebra.TensorProduct.comm_tmul]
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply] at L Rr ⊢
    rw [L, Rr, coact F S₁ C₁ e he c]

end DatumFromFunctor

private theorem
    CategoryTheory.Functor.exists_algEquiv_tensorProduct_descentDatum_of_corepresents_univ
    {R : Type u} [CommRing R] (F : Under (CommRingCat.of R) ⥤ Type v)
    (S₁ : Type u) [CommRing S₁] [Algebra R S₁]
    (C₁ : Type u) [CommRing C₁] [Algebra R C₁] [Algebra S₁ C₁] [IsScalarTower R S₁ C₁]
    (e : ∀ (B : Type u) [CommRing B] [Algebra R B] (j : S₁ →ₐ[R] B),
      F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B))) ≃
        {g : C₁ →ₐ[R] B // g.comp (IsScalarTower.toAlgHom R S₁ C₁) = j})
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1) :
    ∃ φ : C₁ ⊗[R] S₁ ≃ₐ[R] S₁ ⊗[R] C₁,
      φ.toAlgHom.comp (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S₁ C₁) (AlgHom.id R S₁))
          =
        Algebra.TensorProduct.map (AlgHom.id R S₁) (IsScalarTower.toAlgHom R S₁ C₁) ∧
      (Algebra.TensorProduct.map (AlgHom.id R S₁) φ.toAlgHom).comp
          ((Algebra.TensorProduct.assoc R R R S₁ C₁ S₁).toAlgHom.comp
            (Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id R S₁))) =
        (Algebra.TensorProduct.map (AlgHom.id R S₁) (Algebra.TensorProduct.comm R C₁
            S₁).toAlgHom).comp
          ((Algebra.TensorProduct.assoc R R R S₁ C₁ S₁).toAlgHom.comp
            ((Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id R S₁)).comp
              ((Algebra.TensorProduct.assoc R R R C₁ S₁ S₁).symm.toAlgHom.comp
                ((Algebra.TensorProduct.map (AlgHom.id R C₁) (Algebra.TensorProduct.comm R S₁
                    S₁).toAlgHom).comp
                  (Algebra.TensorProduct.assoc R R R C₁ S₁ S₁).toAlgHom)))) ∧
      ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom := by
  refine ⟨DatumFromFunctor.φ F S₁ C₁ e he, ?_, ?_, ?_⟩
  · exact DatumFromFunctor.φ₀_linear F S₁ C₁ e
  · exact DatumFromFunctor.cocycle F S₁ C₁ e he
  · intro D _ _ d x
    exact DatumFromFunctor.intertwine F S₁ C₁ e he _ _ x


open CategoryTheory CategoryTheory.Limits TensorProduct


namespace AffD

variable {R : Type u} [CommRing R]

private def underToAlg {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (k : Under.mk (CommRingCat.ofHom (algebraMap R A)) ⟶ Under.mk (CommRingCat.ofHom (algebraMap R
        B))) :
    A →ₐ[R] B :=
  { toRingHom := (show A →+* B from k.right.hom)
    commutes' := fun r => congrArg (fun (q : CommRingCat.of R ⟶ CommRingCat.of B) => q.hom r)
        (Under.w k) }

private def algToUnder {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (f : A
    →ₐ[R] B) :
    Under.mk (CommRingCat.ofHom (algebraMap R A)) ⟶ Under.mk (CommRingCat.ofHom (algebraMap R B)) :=
  Under.homMk (CommRingCat.ofHom f.toRingHom) (by ext r; exact f.commutes r)

private theorem underToAlg_apply {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R
    B]
    (k : Under.mk (CommRingCat.ofHom (algebraMap R A)) ⟶ Under.mk (CommRingCat.ofHom (algebraMap R
        B))) (a : A) :
    underToAlg k a = k.right.hom a := rfl

private theorem algToUnder_right_hom {A B : Type u} [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] (f : A →ₐ[R] B) (a : A) :
    (algToUnder f).right.hom a = f a := rfl

attribute [local simp] underToAlg_apply algToUnder_right_hom

private theorem algToUnder_underToAlg {A B : Type u} [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B]
    (k : Under.mk (CommRingCat.ofHom (algebraMap R A)) ⟶ Under.mk (CommRingCat.ofHom (algebraMap R
        B))) :
    algToUnder (underToAlg k) = k :=
  Under.UnderMorphism.ext (CommRingCat.hom_ext (RingHom.ext fun _ => rfl))

private theorem underToAlg_algToUnder {A B : Type u} [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] (f : A →ₐ[R] B) :
    underToAlg (algToUnder f) = f :=
  AlgHom.ext fun _ => rfl

private theorem algToUnder_comp {A B D : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R
    B] [CommRing D] [Algebra R D]
    (f : A →ₐ[R] B) (g : B →ₐ[R] D) :
    algToUnder (g.comp f) = algToUnder f ≫ algToUnder g :=
  Under.UnderMorphism.ext (CommRingCat.hom_ext (RingHom.ext fun _ => rfl))

private theorem underToAlg_comp {A B D : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R
    B] [CommRing D] [Algebra R D]
    (k : Under.mk (CommRingCat.ofHom (algebraMap R A)) ⟶ Under.mk (CommRingCat.ofHom (algebraMap R
        B)))
    (g : Under.mk (CommRingCat.ofHom (algebraMap R B)) ⟶ Under.mk (CommRingCat.ofHom (algebraMap R
        D))) :
    underToAlg (k ≫ g) = (underToAlg g).comp (underToAlg k) :=
  AlgHom.ext fun _ => rfl

private def homEquivAlg {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] :
    (Under.mk (CommRingCat.ofHom (algebraMap R A)) ⟶ Under.mk (CommRingCat.ofHom (algebraMap R B)))
        ≃ (A →ₐ[R] B) where
  toFun := underToAlg
  invFun := algToUnder
  left_inv := algToUnder_underToAlg
  right_inv := underToAlg_algToUnder

section Alg

variable (S₁ : Type u) [CommRing S₁] [Algebra R S₁]
  (C₁ : Type u) [CommRing C₁] [Algebra R C₁] [Algebra S₁ C₁] [IsScalarTower R S₁ C₁]
  (φ : C₁ ⊗[R] S₁ ≃ₐ[R] S₁ ⊗[R] C₁)

private abbrev Cst : Subalgebra R C₁ :=
  AlgHom.equalizer (φ.toAlgHom.comp (Algebra.TensorProduct.includeLeft : C₁ →ₐ[R] C₁ ⊗[R] S₁))
    (Algebra.TensorProduct.includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁)

private theorem mem_Cst (a : C₁) : a ∈ Cst S₁ C₁ φ ↔ φ (a ⊗ₜ[R] 1) = (1 : S₁) ⊗ₜ[R] a := by
  rw [Cst, AlgHom.mem_equalizer]; rfl

private def ι₀ : S₁ ⊗[R] ↥(Cst S₁ C₁ φ) →ₐ[R] C₁ :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S₁ C₁) (Cst S₁ C₁ φ).val (fun s a =>
      Commute.all _ _)

private theorem ι₀_tmul (s : S₁) (a : ↥(Cst S₁ C₁ φ)) : ι₀ S₁ C₁ φ (s ⊗ₜ[R] a) = algebraMap S₁ C₁ s
    * (a : C₁) :=
  Algebra.TensorProduct.lift_tmul _ _ _ s a

variable {S₁ C₁ φ}

private theorem algHom_ext_of_surjective (hsurj : Function.Surjective (ι₀ S₁ C₁ φ))
    {D : Type u} [Semiring D] [Algebra R D] {g₁ g₂ : C₁ →ₐ[R] D}
    (h₁ : ∀ s : S₁, g₁ (algebraMap S₁ C₁ s) = g₂ (algebraMap S₁ C₁ s))
    (h₂ : ∀ a : ↥(Cst S₁ C₁ φ), g₁ (a : C₁) = g₂ (a : C₁)) : g₁ = g₂ := by
  apply AlgHom.ext
  intro c
  obtain ⟨z, rfl⟩ := hsurj c
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s a => rw [ι₀_tmul, map_mul, map_mul, h₁, h₂]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

variable (B : Type u) [CommRing B] [Algebra R B]

private theorem includeLeft_injective [Module.FaithfullyFlat R S₁] :
    Function.Injective (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] S₁) := by
  intro x y hxy
  apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := S₁) B
  have := congrArg (TensorProduct.comm R B S₁) hxy
  simpa [Algebra.TensorProduct.includeLeft_apply] using this

variable {B}

private noncomputable def gOf (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) (f : ↥(Cst S₁ C₁ φ)
    →ₐ[R] B) :
    C₁ →ₐ[R] B ⊗[R] S₁ :=
  (Algebra.TensorProduct.lift (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] B ⊗[R] S₁)
      ((Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] S₁).comp f) (fun _ _ => Commute.all _
          _)).comp
    ((AlgEquiv.ofBijective (ι₀ S₁ C₁ φ) hbij).symm.toAlgHom)

private theorem gOf_ι₀ (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) (f : ↥(Cst S₁ C₁ φ)
    →ₐ[R] B) (z : S₁ ⊗[R] ↥(Cst S₁ C₁ φ)) :
    gOf hbij f (ι₀ S₁ C₁ φ z) =
      Algebra.TensorProduct.lift (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] B ⊗[R] S₁)
        ((Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] S₁).comp f) (fun _ _ => Commute.all _
            _) z := by
  unfold gOf
  rw [AlgHom.comp_apply]
  congr 1
  exact (AlgEquiv.ofBijective (ι₀ S₁ C₁ φ) hbij).symm_apply_apply z

private theorem gOf_algebraMap (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) (f : ↥(Cst S₁ C₁ φ)
    →ₐ[R] B) (s : S₁) :
    gOf hbij f (algebraMap S₁ C₁ s) = (1 : B) ⊗ₜ[R] s := by
  have : algebraMap S₁ C₁ s = ι₀ S₁ C₁ φ (s ⊗ₜ[R] 1) := by rw [ι₀_tmul]; simp
  rw [this, gOf_ι₀, Algebra.TensorProduct.lift_tmul]
  simp [Algebra.TensorProduct.includeRight_apply]

private theorem gOf_coe (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) (f : ↥(Cst S₁ C₁ φ)
    →ₐ[R] B) (a : ↥(Cst S₁ C₁ φ)) :
    gOf hbij f (a : C₁) = f a ⊗ₜ[R] (1 : S₁) := by
  have : (a : C₁) = ι₀ S₁ C₁ φ (1 ⊗ₜ[R] a) := by rw [ι₀_tmul]; simp
  rw [this, gOf_ι₀, Algebra.TensorProduct.lift_tmul]
  simp [Algebra.TensorProduct.includeLeft_apply]

private theorem gOf_comp_toAlgHom (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) (f : ↥(Cst S₁ C₁ φ)
    →ₐ[R] B) :
    (gOf hbij f).comp (IsScalarTower.toAlgHom R S₁ C₁) = Algebra.TensorProduct.includeRight := by
  apply AlgHom.ext; intro s
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', gOf_algebraMap]
  rfl

private theorem gOf_unique (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) (f : ↥(Cst S₁ C₁ φ) →ₐ[R] B)
    (g : C₁ →ₐ[R] B ⊗[R] S₁) (hg₁ : g.comp (IsScalarTower.toAlgHom R S₁ C₁)
        = Algebra.TensorProduct.includeRight)
    (hg₂ : ∀ a : ↥(Cst S₁ C₁ φ), g (a : C₁) = f a ⊗ₜ[R] (1 : S₁)) : g = gOf hbij f := by
  apply algHom_ext_of_surjective hbij.2
  · intro s
    rw [gOf_algebraMap]
    have := AlgHom.congr_fun hg₁ s
    rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at this
    rw [this]; rfl
  · intro a; rw [hg₂, gOf_coe]

private noncomputable def fOf [Module.FaithfullyFlat R S₁] (g : C₁ →ₐ[R] B ⊗[R] S₁)
    (hg : ∀ a : ↥(Cst S₁ C₁ φ), g (a : C₁) ∈ Set.range (Algebra.TensorProduct.includeLeft : B
        →ₐ[R] B ⊗[R] S₁)) :
    ↥(Cst S₁ C₁ φ) →ₐ[R] B :=
  ((AlgEquiv.ofInjective (Algebra.TensorProduct.includeLeft : B →ₐ[R] B
      ⊗[R] S₁) (includeLeft_injective B)).symm.toAlgHom).comp
    ((g.comp (Cst S₁ C₁ φ).val).codRestrict (Algebra.TensorProduct.includeLeft : B →ₐ[R] B
        ⊗[R] S₁).range
      (fun a => by obtain ⟨b, hb⟩ := hg a; exact ⟨b, hb⟩))

private theorem includeLeft_fOf [Module.FaithfullyFlat R S₁] (g : C₁ →ₐ[R] B ⊗[R] S₁)
    (hg : ∀ a : ↥(Cst S₁ C₁ φ), g (a : C₁) ∈ Set.range (Algebra.TensorProduct.includeLeft : B
        →ₐ[R] B ⊗[R] S₁))
    (a : ↥(Cst S₁ C₁ φ)) :
    (fOf g hg a) ⊗ₜ[R] (1 : S₁) = g (a : C₁) := by
  show (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] S₁) (fOf g hg a) = g a
  unfold fOf
  rw [AlgHom.comp_apply]
  have := AlgEquiv.ofInjective_apply (Algebra.TensorProduct.includeLeft : B →ₐ[R] B
      ⊗[R] S₁) (includeLeft_injective B)
    ((AlgEquiv.ofInjective (Algebra.TensorProduct.includeLeft : B →ₐ[R] B
        ⊗[R] S₁) (includeLeft_injective B)).symm
      (((g.comp (Cst S₁ C₁ φ).val).codRestrict (Algebra.TensorProduct.includeLeft : B →ₐ[R] B
          ⊗[R] S₁).range
        (fun a => by obtain ⟨b, hb⟩ := hg a; exact ⟨b, hb⟩)) a))
  rw [AlgEquiv.apply_symm_apply] at this
  exact this.symm

private theorem fOf_gOf [Module.FaithfullyFlat R S₁] (hbij : Function.Bijective (ι₀ S₁ C₁ φ))
    (f : ↥(Cst S₁ C₁ φ) →ₐ[R] B)
    (hg : ∀ a : ↥(Cst S₁ C₁ φ), gOf hbij f (a : C₁) ∈ Set.range (Algebra.TensorProduct.includeLeft
        : B →ₐ[R] B ⊗[R] S₁)) :
    fOf (gOf hbij f) hg = f := by
  apply AlgHom.ext; intro a
  apply includeLeft_injective (R := R) (S₁ := S₁) B
  show (fOf (gOf hbij f) hg a) ⊗ₜ[R] (1 : S₁) = f a ⊗ₜ[R] 1
  rw [includeLeft_fOf, gOf_coe]

end Alg

section Main

variable (F : Under (CommRingCat.of R) ⥤ Type v)
  (S₁ : Type u) [CommRing S₁] [Algebra R S₁] [Module.FaithfullyFlat R S₁]
  (C₁ : Type u) [CommRing C₁] [Algebra R C₁] [Algebra S₁ C₁] [IsScalarTower R S₁ C₁]
  (e : ∀ (B : Type u) [CommRing B] [Algebra R B] (j : S₁ →ₐ[R] B),
      F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B))) ≃
        {g : C₁ →ₐ[R] B // g.comp (IsScalarTower.toAlgHom R S₁ C₁) = j})
  (φ : C₁ ⊗[R] S₁ ≃ₐ[R] S₁ ⊗[R] C₁)

private abbrev U (B : Type u) [CommRing B] [Algebra R B] : Under (CommRingCat.of R) := Under.mk
    (CommRingCat.ofHom (algebraMap R B))

private noncomputable abbrev ιU (B : Type u) [CommRing B] [Algebra R B] : U (R := R) B ⟶ U (R := R)
    (B ⊗[R] S₁) :=
  algToUnder (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] S₁)

private theorem e_congr {D : Type u} [CommRing D] [Algebra R D] {j₁ j₂ : S₁ →ₐ[R] D} (h : j₁ = j₂)
    (x : F.obj (U (R := R) D)) : ((e D j₁ x).1 : C₁ →ₐ[R] D) = (e D j₂ x).1 := by
  subst h; rfl

variable {F S₁ C₁}

private noncomputable def gPt {B : Type u} [CommRing B] [Algebra R B] (y : F.obj (U (R := R) (B
    ⊗[R] S₁))) : C₁ →ₐ[R] B ⊗[R] S₁ :=
  ((e (B ⊗[R] S₁) (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] B ⊗[R] S₁)) y).1

private theorem gPt_comp {B : Type u} [CommRing B] [Algebra R B] (y : F.obj (U (R := R) (B
    ⊗[R] S₁))) :
    (gPt e y).comp (IsScalarTower.toAlgHom R S₁ C₁) = Algebra.TensorProduct.includeRight :=
  ((e (B ⊗[R] S₁) (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] B ⊗[R] S₁)) y).2

private theorem descends_iff
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hsurj : Function.Surjective (ι₀ S₁ C₁ φ))
    {B : Type u} [CommRing B] [Algebra R B] (y : F.obj (U (R := R) (B ⊗[R] S₁))) :
    F.map (pushout.inl (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) y = F.map (pushout.inr (ιU (R := R)
        S₁ B) (ιU (R := R) S₁ B)) y ↔
      ∀ a : ↥(Cst S₁ C₁ φ), gPt e y (a : C₁) ∈ Set.range (Algebra.TensorProduct.includeLeft : B
          →ₐ[R] B ⊗[R] S₁) := by
  classical

  set P := pushout (ιU (R := R) S₁ B) (ιU (R := R) S₁ B) with hP
  letI instD : Algebra R (P.right : Type u) := (show R →+* P.right from P.hom.hom).toAlgebra
  have hPU : U (R := R) (P.right : Type u) = P := rfl
  let inlA : B ⊗[R] S₁ →ₐ[R] (P.right : Type u) := underToAlg (A := B ⊗[R] S₁) (B := (P.right :
      Type u)) (pushout.inl (ιU (R := R) S₁ B) (ιU (R := R) S₁ B))
  let inrA : B ⊗[R] S₁ →ₐ[R] (P.right : Type u) := underToAlg (A := B ⊗[R] S₁) (B := (P.right :
      Type u)) (pushout.inr (ιU (R := R) S₁ B) (ιU (R := R) S₁ B))
  have hinl : algToUnder inlA = pushout.inl (ιU (R := R) S₁ B) (ιU (R := R) S₁ B) :=
      algToUnder_underToAlg _
  have hinr : algToUnder inrA = pushout.inr (ιU (R := R) S₁ B) (ιU (R := R) S₁ B) :=
      algToUnder_underToAlg _

  have hcond : ∀ b : B, inlA (b ⊗ₜ[R] 1) = inrA (b ⊗ₜ[R] 1) := fun b =>
    congrArg (fun (k : U (R := R) B ⟶ P) => k.right.hom b) (pushout.condition (f := ιU (R := R) S₁
        B) (g := ιU (R := R) S₁ B))

  let inR : S₁ →ₐ[R] B ⊗[R] S₁ := Algebra.TensorProduct.includeRight
  let d : S₁ ⊗[R] S₁ →ₐ[R] (P.right : Type u) :=
    Algebra.TensorProduct.lift (inlA.comp inR) (inrA.comp inR) (fun _ _ => Commute.all _ _)
  have hd₁ : d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁) = inlA.comp inR :=
    Algebra.TensorProduct.lift_comp_includeLeft _ _ _
  have hd₂ : d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁) = inrA.comp inR := by
    apply AlgHom.ext; intro s
    show d ((1 : S₁) ⊗ₜ[R] s) = inrA (inR s)
    rw [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, map_one, map_one, one_mul,
        AlgHom.comp_apply]

  have hgS : ∀ s : S₁, gPt e y (algebraMap S₁ C₁ s) = (1 : B) ⊗ₜ[R] s := by
    intro s
    have := AlgHom.congr_fun (gPt_comp e y) s
    rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at this
    rw [this]; rfl

  have hinl' : Under.homMk (CommRingCat.ofHom inlA.toRingHom) (by ext r; exact inlA.commutes r) =
      pushout.inl (ιU (R := R) S₁ B) (ιU (R := R) S₁ B) := hinl
  have hinr' : Under.homMk (CommRingCat.ofHom inrA.toRingHom) (by ext r; exact inrA.commutes r) =
      pushout.inr (ιU (R := R) S₁ B) (ιU (R := R) S₁ B) := hinr
  have he₁ : ((e (P.right : Type u) (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁
      ⊗[R] S₁)))
      (F.map (pushout.inl (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) y)).1 = inlA.comp (gPt e y) := by
    rw [e_congr F S₁ C₁ e hd₁]
    have := he (B ⊗[R] S₁) (P.right : Type u) inR inlA y
    have hF : F.map (pushout.inl (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) y =
        F.map (Under.homMk (CommRingCat.ofHom inlA.toRingHom) (by ext r; exact inlA.commutes r))
            y :=
      congrArg (fun k => F.map k y) hinl'.symm
    rw [hF]; exact this
  have he₂ : ((e (P.right : Type u) (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁
      ⊗[R] S₁)))
      (F.map (pushout.inr (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) y)).1 = inrA.comp (gPt e y) := by
    rw [e_congr F S₁ C₁ e hd₂]
    have := he (B ⊗[R] S₁) (P.right : Type u) inR inrA y
    have hF : F.map (pushout.inr (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) y =
        F.map (Under.homMk (CommRingCat.ofHom inrA.toRingHom) (by ext r; exact inrA.commutes r))
            y :=
      congrArg (fun k => F.map k y) hinr'.symm
    rw [hF]; exact this

  have hstar := hφ (P.right : Type u) d (F.map (pushout.inr (ιU (R := R) S₁ B) (ιU (R := R) S₁ B))
      y)
  rw [he₂] at hstar
  set G : C₁ →ₐ[R] (P.right : Type u) := ((e (P.right : Type u) (d.comp
      (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁)))
      (F.map (pushout.inr (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) y)).1 with hG
  have hGS : G.comp (IsScalarTower.toAlgHom R S₁ C₁) = d.comp Algebra.TensorProduct.includeLeft :=
    ((e (P.right : Type u) (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁)))
      (F.map (pushout.inr (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) y)).2

  have hGa : ∀ a : ↥(Cst S₁ C₁ φ), G (a : C₁) = inrA (gPt e y (a : C₁)) := by
    intro a
    have := AlgHom.congr_fun hstar ((a : C₁) ⊗ₜ[R] (1 : S₁))
    have hφa : φ.toAlgHom ((a : C₁) ⊗ₜ[R] (1 : S₁)) = (1 : S₁) ⊗ₜ[R] (a : C₁) := (mem_Cst S₁ C₁ φ
        (a : C₁)).mp a.2
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.lift_tmul, map_one, mul_one] at this
    rw [hφa, Algebra.TensorProduct.lift_tmul, map_one, one_mul] at this
    exact this

  have key : F.map (pushout.inl (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) y =
      F.map (pushout.inr (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) y ↔ inlA.comp (gPt e y) = G := by
    constructor
    · intro h
      rw [← he₁, h]
    · intro h
      apply (e (P.right : Type u) (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁
          ⊗[R] S₁))).injective
      apply Subtype.ext
      rw [he₁, h]
  rw [key]
  constructor
  ·
    intro h a
    have h1 : inlA (gPt e y (a : C₁)) = inrA (gPt e y (a : C₁)) := by
      rw [← hGa a, ← h]; rfl

    let T : Type u := (B ⊗[R] S₁) ⊗[B] (B ⊗[R] S₁)
    let j₁ : B ⊗[R] S₁ →ₐ[R] T := Algebra.TensorProduct.includeLeft
    let j₂ : B ⊗[R] S₁ →ₐ[R] T :=
      (Algebra.TensorProduct.includeRight : (B ⊗[R] S₁) →ₐ[B] (B ⊗[R] S₁) ⊗[B] (B
          ⊗[R] S₁)).restrictScalars R
    have hcompat : ιU (R := R) S₁ B ≫ algToUnder (A := B ⊗[R] S₁) (B := T) j₁ = ιU (R := R) S₁ B
        ≫ algToUnder (A := B ⊗[R] S₁) (B := T) j₂ := by
      apply Under.UnderMorphism.ext
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro b
      change B at b
      show j₁ (b ⊗ₜ[R] (1 : S₁)) = j₂ (b ⊗ₜ[R] (1 : S₁))
      show (b ⊗ₜ[R] (1 : S₁)) ⊗ₜ[B] (1 : B ⊗[R] S₁) = (1 : B ⊗[R] S₁) ⊗ₜ[B] (b ⊗ₜ[R] (1 : S₁))
      have hb : b ⊗ₜ[R] (1 : S₁) = b • (1 : B ⊗[R] S₁) := by
        rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hb, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    let desc : P ⟶ U (R := R) T := pushout.desc (algToUnder (A := B ⊗[R] S₁) (B := T) j₁)
        (algToUnder (A := B ⊗[R] S₁) (B := T) j₂) hcompat
    have e1 : ∀ z : B ⊗[R] S₁, desc.right.hom (inlA z) = j₁ z := fun z =>
      congrArg (fun (k : U (R := R) (B ⊗[R] S₁) ⟶ U (R := R) T) => k.right.hom z) (pushout.inl_desc
          _ _ hcompat)
    have e2 : ∀ z : B ⊗[R] S₁, desc.right.hom (inrA z) = j₂ z := fun z =>
      congrArg (fun (k : U (R := R) (B ⊗[R] S₁) ⟶ U (R := R) T) => k.right.hom z) (pushout.inr_desc
          _ _ hcompat)
    have h2 : (gPt e y (a : C₁)) ⊗ₜ[B] (1 : B ⊗[R] S₁) = (1 : B ⊗[R] S₁)
        ⊗ₜ[B] (gPt e y (a : C₁)) := by
      have := e1 (gPt e y (a : C₁))
      rw [h1, e2] at this
      exact this.symm
    obtain ⟨b₀, hb₀⟩ :=
      (Algebra.IsEffective.of_faithfullyFlat B (B ⊗[R] S₁) (gPt e y (a : C₁))).mp
        (by rw [Algebra.TensorProduct.includeLeftSubRight_apply, h2, sub_self])
    exact ⟨b₀, hb₀⟩
  ·
    intro h
    apply algHom_ext_of_surjective hsurj
    · intro s
      rw [AlgHom.comp_apply, hgS]
      have := AlgHom.congr_fun hGS s
      rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hd₁] at this
      rw [this]; rfl
    · intro a
      obtain ⟨b₀, hb₀⟩ := h a
      rw [AlgHom.comp_apply, hGa, ← hb₀]
      exact hcond b₀

private theorem hsheaf_at
    (hsheaf : ∀ (B B' : Under (CommRingCat.of R)) (φ : B ⟶ B'),
      φ.right.hom.Flat → Function.Surjective (PrimeSpectrum.comap φ.right.hom) →
        Function.Injective (F.map φ) ∧
        ∀ y : F.obj B', F.map (pushout.inl φ φ) y = F.map (pushout.inr φ φ) y → ∃ x : F.obj B,
            F.map φ x = y)
    (B : Type u) [CommRing B] [Algebra R B] :
    Function.Injective (F.map (ιU (R := R) S₁ B)) ∧
      ∀ y : F.obj (U (R := R) (B ⊗[R] S₁)),
        F.map (pushout.inl (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) y
            = F.map (pushout.inr (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) y →
          ∃ x : F.obj (U (R := R) B), F.map (ιU (R := R) S₁ B) x = y := by
  apply hsheaf (U (R := R) B) (U (R := R) (B ⊗[R] S₁)) (ιU (R := R) S₁ B)
  · show (algebraMap B (B ⊗[R] S₁)).Flat
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  · show Function.Surjective (PrimeSpectrum.comap (algebraMap B (B ⊗[R] S₁)))
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat

private theorem descends_map {B : Type u} [CommRing B] [Algebra R B] (x : F.obj (U (R := R) B)) :
    F.map (pushout.inl (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) (F.map (ιU (R := R) S₁ B) x) =
      F.map (pushout.inr (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) (F.map (ιU (R := R) S₁ B) x) := by
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, pushout.condition]

private noncomputable def yOf (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) {B : Type u} [CommRing B]
    [Algebra R B]
    (f : ↥(Cst S₁ C₁ φ) →ₐ[R] B) : F.obj (U (R := R) (B ⊗[R] S₁)) :=
  (e (B ⊗[R] S₁) (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] B ⊗[R] S₁)).symm ⟨gOf hbij f,
      gOf_comp_toAlgHom hbij f⟩

private theorem gPt_yOf (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) {B : Type u} [CommRing B] [Algebra
    R B]
    (f : ↥(Cst S₁ C₁ φ) →ₐ[R] B) : gPt e (yOf e φ hbij f) = gOf hbij f := by
  unfold gPt yOf
  rw [Equiv.apply_symm_apply]

private theorem fOf_congr {B : Type u} [CommRing B] [Algebra R B] {g₁ g₂ : C₁ →ₐ[R] B
    ⊗[R] S₁} (h : g₁ = g₂)
    (h₁ : ∀ a : ↥(Cst S₁ C₁ φ), g₁ (a : C₁) ∈ Set.range (Algebra.TensorProduct.includeLeft : B
        →ₐ[R] B ⊗[R] S₁))
    (h₂ : ∀ a : ↥(Cst S₁ C₁ φ), g₂ (a : C₁) ∈ Set.range (Algebra.TensorProduct.includeLeft : B
        →ₐ[R] B ⊗[R] S₁)) :
    fOf g₁ h₁ = fOf g₂ h₂ := by
  subst h; rfl

section Assembly

private noncomputable def theta
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) {B : Type u} [CommRing B] [Algebra R B] (x : F.obj
        (U (R := R) B)) : ↥(Cst S₁ C₁ φ) →ₐ[R] B :=
  fOf (gPt e (F.map (ιU (R := R) S₁ B) x)) ((descends_iff e φ he hφ hbij.2 _).mp (descends_map x))

private theorem includeLeft_theta
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) {B : Type u} [CommRing B] [Algebra R B] (x : F.obj
        (U (R := R) B)) (a : ↥(Cst S₁ C₁ φ)) :
    (theta e φ he hφ hbij x a) ⊗ₜ[R] (1 : S₁) = gPt e (F.map (ιU (R := R) S₁ B) x) (a : C₁) :=
  includeLeft_fOf _ _ a

private theorem yOf_descends
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) {B : Type u} [CommRing B] [Algebra R B] (f : ↥(Cst S₁
        C₁ φ) →ₐ[R] B) :
    F.map (pushout.inl (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) (yOf e φ hbij f) =
      F.map (pushout.inr (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) (yOf e φ hbij f) := by
  rw [descends_iff e φ he hφ hbij.2]
  intro a
  rw [gPt_yOf, gOf_coe]
  exact ⟨f a, rfl⟩

private noncomputable def psi
    (hsheaf : ∀ (B B' : Under (CommRingCat.of R)) (φ : B ⟶ B'),
      φ.right.hom.Flat → Function.Surjective (PrimeSpectrum.comap φ.right.hom) →
        Function.Injective (F.map φ) ∧
        ∀ y : F.obj B', F.map (pushout.inl φ φ) y = F.map (pushout.inr φ φ) y → ∃ x : F.obj B,
            F.map φ x = y)
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) {B : Type u} [CommRing B] [Algebra R B] (f : ↥(Cst S₁
        C₁ φ) →ₐ[R] B) : F.obj (U (R := R) B) :=
  ((hsheaf_at (S₁ := S₁) hsheaf B).2 (yOf e φ hbij f) (yOf_descends e φ he hφ hbij f)).choose

private theorem map_psi
    (hsheaf : ∀ (B B' : Under (CommRingCat.of R)) (φ : B ⟶ B'),
      φ.right.hom.Flat → Function.Surjective (PrimeSpectrum.comap φ.right.hom) →
        Function.Injective (F.map φ) ∧
        ∀ y : F.obj B', F.map (pushout.inl φ φ) y = F.map (pushout.inr φ φ) y → ∃ x : F.obj B,
            F.map φ x = y)
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) {B : Type u} [CommRing B] [Algebra R B] (f : ↥(Cst S₁
        C₁ φ) →ₐ[R] B) :
    F.map (ιU (R := R) S₁ B) (psi e φ hsheaf he hφ hbij f) = yOf e φ hbij f :=
  ((hsheaf_at (S₁ := S₁) hsheaf B).2 (yOf e φ hbij f) (yOf_descends e φ he hφ hbij f)).choose_spec

private theorem theta_psi
    (hsheaf : ∀ (B B' : Under (CommRingCat.of R)) (φ : B ⟶ B'),
      φ.right.hom.Flat → Function.Surjective (PrimeSpectrum.comap φ.right.hom) →
        Function.Injective (F.map φ) ∧
        ∀ y : F.obj B', F.map (pushout.inl φ φ) y = F.map (pushout.inr φ φ) y → ∃ x : F.obj B,
            F.map φ x = y)
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) {B : Type u} [CommRing B] [Algebra R B] (f : ↥(Cst S₁
        C₁ φ) →ₐ[R] B) :
    theta e φ he hφ hbij (psi e φ hsheaf he hφ hbij f) = f := by
  have h : gPt e (F.map (ιU (R := R) S₁ B) (psi e φ hsheaf he hφ hbij f)) = gOf hbij f := by
    rw [map_psi, gPt_yOf]
  unfold theta
  rw [fOf_congr φ h _ (fun a => by rw [gOf_coe]; exact ⟨f a, rfl⟩)]
  exact fOf_gOf hbij f _

private theorem gPt_map_eq_gOf_theta
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) {B : Type u} [CommRing B] [Algebra R B] (x : F.obj
        (U (R := R) B)) :
    gPt e (F.map (ιU (R := R) S₁ B) x) = gOf hbij (theta e φ he hφ hbij x) :=
  gOf_unique hbij _ _ (gPt_comp e _) (fun a => (includeLeft_theta e φ he hφ hbij x a).symm)

private theorem psi_theta
    (hsheaf : ∀ (B B' : Under (CommRingCat.of R)) (φ : B ⟶ B'),
      φ.right.hom.Flat → Function.Surjective (PrimeSpectrum.comap φ.right.hom) →
        Function.Injective (F.map φ) ∧
        ∀ y : F.obj B', F.map (pushout.inl φ φ) y = F.map (pushout.inr φ φ) y → ∃ x : F.obj B,
            F.map φ x = y)
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) {B : Type u} [CommRing B] [Algebra R B] (x : F.obj
        (U (R := R) B)) :
    psi e φ hsheaf he hφ hbij (theta e φ he hφ hbij x) = x := by
  apply (hsheaf_at (S₁ := S₁) hsheaf B).1
  rw [map_psi]
  unfold yOf
  apply (e (B ⊗[R] S₁) (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] B ⊗[R] S₁)).symm_apply_eq.mpr
  apply Subtype.ext
  exact (gPt_map_eq_gOf_theta e φ he hφ hbij x).symm

private noncomputable def equivB
    (hsheaf : ∀ (B B' : Under (CommRingCat.of R)) (φ : B ⟶ B'),
      φ.right.hom.Flat → Function.Surjective (PrimeSpectrum.comap φ.right.hom) →
        Function.Injective (F.map φ) ∧
        ∀ y : F.obj B', F.map (pushout.inl φ φ) y = F.map (pushout.inr φ φ) y → ∃ x : F.obj B,
            F.map φ x = y)
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) (B : Type u) [CommRing B] [Algebra R B] : (↥(Cst S₁ C₁
        φ) →ₐ[R] B) ≃ F.obj (U (R := R) B) where
  toFun := psi e φ hsheaf he hφ hbij
  invFun := theta e φ he hφ hbij
  left_inv := theta_psi e φ hsheaf he hφ hbij
  right_inv := psi_theta e φ hsheaf he hφ hbij

private theorem psi_natural
    (hsheaf : ∀ (B B' : Under (CommRingCat.of R)) (φ : B ⟶ B'),
      φ.right.hom.Flat → Function.Surjective (PrimeSpectrum.comap φ.right.hom) →
        Function.Injective (F.map φ) ∧
        ∀ y : F.obj B', F.map (pushout.inl φ φ) y = F.map (pushout.inr φ φ) y → ∃ x : F.obj B,
            F.map φ x = y)
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) {B B' : Type u} [CommRing B] [Algebra R B] [CommRing
        B'] [Algebra R B']
    (ψ : B →ₐ[R] B') (f : ↥(Cst S₁ C₁ φ) →ₐ[R] B) :
    psi e φ hsheaf he hφ hbij (ψ.comp f) = F.map (algToUnder ψ) (psi e φ hsheaf he hφ hbij f) := by
  apply (hsheaf_at (S₁ := S₁) hsheaf B').1
  rw [map_psi]

  let ψ' : B ⊗[R] S₁ →ₐ[R] B' ⊗[R] S₁ := Algebra.TensorProduct.map ψ (AlgHom.id R S₁)
  have hsq : algToUnder ψ ≫ ιU (R := R) S₁ B' = ιU (R := R) S₁ B ≫ algToUnder ψ' := by
    rw [ιU, ιU, ← algToUnder_comp, ← algToUnder_comp]
    congr 1
  rw [← Functor.map_comp_apply, hsq, Functor.map_comp_apply, map_psi]

  apply (e (B' ⊗[R] S₁) (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] B' ⊗[R] S₁)).injective
  apply Subtype.ext
  have hj : ψ'.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] B ⊗[R] S₁) =
      (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] B' ⊗[R] S₁) := by
    apply AlgHom.ext; intro s
    simp [ψ', Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  have h1 : ((e (B' ⊗[R] S₁) (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] B' ⊗[R] S₁))
      (F.map (algToUnder ψ') (yOf e φ hbij f))).1 = ψ'.comp (gOf hbij f) := by
    rw [← e_congr F S₁ C₁ e hj]
    have := he (B ⊗[R] S₁) (B' ⊗[R] S₁) Algebra.TensorProduct.includeRight ψ' (yOf e φ hbij f)
    refine this.trans ?_
    congr 1
    exact gPt_yOf e φ hbij f
  rw [h1]
  show gPt e (yOf e φ hbij (ψ.comp f)) = ψ'.comp (gOf hbij f)
  rw [gPt_yOf]
  symm
  apply gOf_unique hbij
  · rw [AlgHom.comp_assoc, gOf_comp_toAlgHom, hj]
  · intro a
    rw [AlgHom.comp_apply, gOf_coe]
    simp [ψ', Algebra.TensorProduct.map_tmul]

end Assembly

end Main

end AffD

open AffD in
private theorem CategoryTheory.Functor.exists_corepresentableBy_of_descentDatum_of_bijective_univ
    {R : Type u} [CommRing R] (F : Under (CommRingCat.of R) ⥤ Type v)
    (hsheaf : ∀ (B B' : Under (CommRingCat.of R)) (φ : B ⟶ B'),
      φ.right.hom.Flat → Function.Surjective (PrimeSpectrum.comap φ.right.hom) →
        Function.Injective (F.map φ) ∧
        ∀ y : F.obj B', F.map (pushout.inl φ φ) y = F.map (pushout.inr φ φ) y → ∃ x : F.obj B,
            F.map φ x = y)
    (S₁ : Type u) [CommRing S₁] [Algebra R S₁] [Module.FaithfullyFlat R S₁]
    (C₁ : Type u) [CommRing C₁] [Algebra R C₁] [Algebra S₁ C₁] [IsScalarTower R S₁ C₁]
    (e : ∀ (B : Type u) [CommRing B] [Algebra R B] (j : S₁ →ₐ[R] B),
      F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B))) ≃
        {g : C₁ →ₐ[R] B // g.comp (IsScalarTower.toAlgHom R S₁ C₁) = j})
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (φ : C₁ ⊗[R] S₁ ≃ₐ[R] S₁ ⊗[R] C₁)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hbij : Function.Bijective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S₁ C₁)
      (AlgHom.equalizer (φ.toAlgHom.comp (Algebra.TensorProduct.includeLeft : C₁ →ₐ[R] C₁ ⊗[R] S₁))
        (Algebra.TensorProduct.includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁)).val (fun s a => Commute.all _
            _))) :
    ∃ C : Under (CommRingCat.of R), Nonempty (F.CorepresentableBy C) := by
  classical
  have hbij' : Function.Bijective (ι₀ S₁ C₁ φ) := hbij
  refine ⟨U (R := R) ↥(Cst S₁ C₁ φ), ⟨?_⟩⟩
  exact
    { homEquiv := fun {Y} =>
        letI : Algebra R (Y.right : Type u) := (show R →+* Y.right from Y.hom.hom).toAlgebra
        (homEquivAlg (R := R) (A := ↥(Cst S₁ C₁ φ)) (B := (Y.right : Type u))).trans
          (equivB e φ hsheaf he hφ hbij' (Y.right : Type u))
      homEquiv_comp := by
        intro Y Y' g k
        letI iY : Algebra R (Y.right : Type u) := (show R →+* Y.right from Y.hom.hom).toAlgebra
        letI iY' : Algebra R (Y'.right : Type u) := (show R →+* Y'.right from Y'.hom.hom).toAlgebra
        show psi e φ hsheaf he hφ hbij' (underToAlg (A := ↥(Cst S₁ C₁ φ)) (B := (Y'.right : Type
            u)) (k ≫ g)) =
          F.map g (psi e φ hsheaf he hφ hbij' (underToAlg (A := ↥(Cst S₁ C₁ φ)) (B := (Y.right :
              Type u)) k))
        have hg : algToUnder (underToAlg (A := (Y.right : Type u)) (B := (Y'.right : Type u)) g)
            = g :=
          algToUnder_underToAlg _
        have h1 : underToAlg (A := ↥(Cst S₁ C₁ φ)) (B := (Y'.right : Type u)) (k ≫ g) =
            (underToAlg (A := (Y.right : Type u)) (B := (Y'.right : Type u)) g).comp
              (underToAlg (A := ↥(Cst S₁ C₁ φ)) (B := (Y.right : Type u)) k) :=
          underToAlg_comp (A := ↥(Cst S₁ C₁ φ)) (B := (Y.right : Type u)) (D := (Y'.right : Type
              u)) k g
        rw [h1, psi_natural e φ hsheaf he hφ hbij']
        exact congrArg (fun (m : Y ⟶ Y') => F.map m (psi e φ hsheaf he hφ hbij' (underToAlg
            (A := ↥(Cst S₁ C₁ φ)) (B := (Y.right : Type u)) k))) hg }


open CategoryTheory CategoryTheory.Limits TensorProduct Algebra.TensorProduct


namespace AffDescBridge

variable {R : Type u} [CommRing R]

private abbrev objOf (D : Type u) [CommRing D] [Algebra R D] : Under (CommRingCat.of R) :=
  Under.mk (CommRingCat.ofHom (algebraMap R D))

private abbrev homOf {D D' : Type u} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (ψ : D
    →ₐ[R] D') :
    objOf (R := R) D ⟶ objOf D' :=
  Under.homMk (CommRingCat.ofHom ψ.toRingHom) (by ext r; exact ψ.commutes r)

private lemma homOf_comp {D D' D'' : Type u} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R
    D'] [CommRing D''] [Algebra R D'']
    (ψ : D →ₐ[R] D') (ψ' : D' →ₐ[R] D'') : homOf (ψ'.comp ψ) = homOf ψ ≫ homOf ψ' := by
  apply Under.UnderMorphism.ext; rfl

private scoped instance instAlgebraRight (C₁ : Under (CommRingCat.of R)) : Algebra R (C₁.right :
    Type u) :=
  (show R →+* C₁.right from C₁.hom.hom).toAlgebra

variable (C₁ : Under (CommRingCat.of R))

private lemma algebraMap_right_apply (r : R) : algebraMap R (C₁.right : Type u) r = C₁.hom.hom r :=
    rfl

private abbrev algOf {D : Type u} [CommRing D] [Algebra R D] (q : C₁ ⟶ objOf (R := R) D) :
    (C₁.right : Type u) →ₐ[R] D :=
  { toRingHom := (show (C₁.right : Type u) →+* D from q.right.hom),
    commutes' := fun r => congrArg (fun (k : CommRingCat.of R ⟶ CommRingCat.of D) => k.hom r)
        (Under.w q) }

private abbrev homOfC {D : Type u} [CommRing D] [Algebra R D] (g : (C₁.right : Type u) →ₐ[R] D) :
    C₁ ⟶ objOf (R := R) D :=
  Under.homMk (CommRingCat.ofHom g.toRingHom) (by ext r; exact g.commutes r)

private lemma algOf_homOfC {D : Type u} [CommRing D] [Algebra R D] (g : (C₁.right : Type u)
    →ₐ[R] D) :
    algOf C₁ (homOfC C₁ g) = g := AlgHom.ext fun _ => rfl

private lemma homOfC_algOf {D : Type u} [CommRing D] [Algebra R D] (q : C₁ ⟶ objOf (R := R) D) :
    homOfC C₁ (algOf C₁ q) = q := by
  apply Under.UnderMorphism.ext; ext a; rfl

private lemma algOf_comp {D D' : Type u} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (q : C₁ ⟶ objOf (R := R) D) (ψ : D →ₐ[R] D') :
    algOf C₁ (q ≫ homOf ψ) = ψ.comp (algOf C₁ q) := AlgHom.ext fun _ => rfl

end AffDescBridge

@[expose] public section

open AffDescBridge in
/-- Faithfully flat descent for corepresentability: a functor on `R`-algebras satisfying the
faithfully flat sheaf condition, whose restriction to `S₁`-algebras is corepresented by `C₁`
for a faithfully flat `R`-algebra `S₁`, is itself corepresentable. -/
theorem CategoryTheory.Functor.exists_corepresentableBy_of_faithfullyFlat_of_sheaf_univ
    {R : Type u} [CommRing R] (F : Under (CommRingCat.of R) ⥤ Type v)
    (hsheaf : ∀ (B B' : Under (CommRingCat.of R)) (φ : B ⟶ B'),
      φ.right.hom.Flat → Function.Surjective (PrimeSpectrum.comap φ.right.hom) →
        Function.Injective (F.map φ) ∧
        ∀ y : F.obj B', F.map (pushout.inl φ φ) y = F.map (pushout.inr φ φ) y → ∃ x : F.obj B,
            F.map φ x = y)
    (S₁ : Type u) [CommRing S₁] [Algebra R S₁] (hflat : (algebraMap R S₁).Flat)
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S₁)))
    (C₁ : Under (CommRingCat.of R)) (c : Under.mk (CommRingCat.ofHom (algebraMap R S₁)) ⟶ C₁)
    (e : ∀ (B' : Under (CommRingCat.of R)) (b : Under.mk (CommRingCat.ofHom (algebraMap R S₁)) ⟶
        B'),
      F.obj B' ≃ {g : C₁ ⟶ B' // c ≫ g = b})
    (he : ∀ (B' B'' : Under (CommRingCat.of R)) (b : Under.mk (CommRingCat.ofHom (algebraMap R S₁))
        ⟶ B')
      (ψ : B' ⟶ B'') (x : F.obj B'),
      ((e B'' (b ≫ ψ)) (F.map ψ x)).1 = ((e B' b) x).1 ≫ ψ) :
    ∃ C : Under (CommRingCat.of R), Nonempty (F.CorepresentableBy C) := by
  letI iSC : Algebra S₁ (C₁.right : Type u) := (show S₁ →+* C₁.right from c.right.hom).toAlgebra
  have hcw : ∀ r : R, (show S₁ →+* C₁.right from c.right.hom) (algebraMap R S₁ r)
      = algebraMap R C₁.right r :=
    fun r => congrArg (fun (k : CommRingCat.of R ⟶ C₁.right) => k.hom r) (Under.w c)
  letI iT : IsScalarTower R S₁ (C₁.right : Type u) := IsScalarTower.of_algebraMap_eq (fun r =>
      (hcw r).symm)
  haveI : Module.Flat R S₁ := by
    have h := hflat
    rwa [RingHom.flat_algebraMap_iff] at h
  haveI : Module.FaithfullyFlat R S₁ := Module.FaithfullyFlat.of_comap_surjective hsurj

  have hc_alg : ∀ s : S₁, (IsScalarTower.toAlgHom R S₁ (C₁.right : Type u)) s = c.right.hom s :=
      fun s => rfl

  have key : ∀ (B : Type u) [CommRing B] [Algebra R B] (j : S₁ →ₐ[R] B) (q : C₁ ⟶ objOf (R := R) B),
      c ≫ q = homOf j ↔ (algOf C₁ q).comp (IsScalarTower.toAlgHom R S₁ (C₁.right : Type u))
          = j := by
    intro B _ _ j q
    constructor
    · intro h
      apply AlgHom.ext
      intro s
      have := congrArg (fun (k : (objOf (R := R) S₁) ⟶ objOf B) => k.right.hom s) h
      exact this
    · intro h
      apply Under.UnderMorphism.ext
      ext s
      exact congrArg (fun (k : S₁ →ₐ[R] B) => k s) h

  let e' : ∀ (B : Type u) [CommRing B] [Algebra R B] (j : S₁ →ₐ[R] B),
      F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B))) ≃
        {g : (C₁.right : Type u) →ₐ[R] B // g.comp (IsScalarTower.toAlgHom R S₁ (C₁.right : Type
            u)) = j} :=
    fun B _ _ j => (e (objOf B) (homOf j)).trans
      { toFun := fun q => ⟨algOf C₁ q.1, (key B j q.1).mp q.2⟩
        invFun := fun g => ⟨homOfC C₁ g.1, (key B j _).mpr (by rw [algOf_homOfC]; exact g.2)⟩
        left_inv := fun q => Subtype.ext (homOfC_algOf C₁ q.1)
        right_inv := fun g => Subtype.ext (algOf_homOfC C₁ g.1) }
  have e'_val : ∀ (B : Type u) [CommRing B] [Algebra R B] (j : S₁ →ₐ[R] B)
      (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))), ((e' B j) x).1
          = algOf C₁ ((e (objOf B) (homOf j)) x).1 :=
    fun B _ _ j x => rfl

  have e_congr : ∀ (B' : Under (CommRingCat.of R)) (b b' : Under.mk (CommRingCat.ofHom (algebraMap
      R S₁)) ⟶ B')
      (h : b = b') (y : F.obj B'), ((e B' b) y).1 = ((e B' b') y).1 := by
    intro B' b b' h y; subst h; rfl
  have he' : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e' B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e' B j) x).1 := by
    intro B B' _ _ _ _ j ψ x
    rw [e'_val, e'_val, ← algOf_comp]
    congr 1
    rw [e_congr (objOf B') (homOf (ψ.comp j)) (homOf j ≫ homOf ψ) (homOf_comp j ψ)]
    exact he (objOf B) (objOf B') (homOf j) (homOf ψ) x
  obtain ⟨φ, hlin, hcoc, hφ⟩ :=
    CategoryTheory.Functor.exists_algEquiv_tensorProduct_descentDatum_of_corepresents_univ F S₁
        (C₁.right : Type u) e' he'
  have hbij := Algebra.bijective_tensorProduct_equalizer_of_faithfullyFlat_of_descentDatum (S := R)
      S₁
    (C₁.right : Type u) φ hlin hcoc
  exact CategoryTheory.Functor.exists_corepresentableBy_of_descentDatum_of_bijective_univ F hsheaf
      S₁ (C₁.right : Type u)
    e' he' φ hφ hbij

