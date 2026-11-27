/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModuleResolutionAsphericity
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Normalized obstruction fillers from module asphericity

Let `P → const M` be an augmented simplicial module over a ring `R`, and suppose
its normalized augmentation is a quasi-isomorphism. The degree-zero augmentation is
surjective and its kernel is the image of the first normalized differential. The
normalized complex is exact in every positive degree.

These statements give fillers in the simplicial module itself. An element in the
augmentation kernel in degree zero is the zero face of an edge whose other face and
augmentation vanish. In positive degree, an element with all faces zero is the zero
face of a higher simplex with all remaining faces and augmentation zero. The ring and
module-carrier universes are independent.

See Loday, §3.5.3, and the Stacks Project, Tag 0194.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v

namespace AlgebraicTopology.ModuleResolutionAsphericity

open ModuleMooreComplex

variable {R : Type u} [Ring R]
  (P : SimplicialObject.Augmented (ModuleCat.{v} R))

variable [QuasiIso (augmentation P)]

/--
If the normalized augmentation is a quasi-isomorphism, its induced map on degree-zero
opcycles is an isomorphism.
-/
theorem augmentation_opcyclesMap_isIso :
    IsIso (HomologicalComplex.opcyclesMap (augmentation P) 0) := by
  let L := (ChainComplex.single₀ (ModuleCat.{v} R)).obj P.right
  have h := ChainComplex.isoHomologyι₀_inv_naturality (augmentation P)
  have he : HomologicalComplex.opcyclesMap (augmentation P) 0 =
      ((normalized P).isoHomologyι₀.inv ≫ HomologicalComplex.homologyMap (augmentation P) 0) ≫
        L.isoHomologyι₀.hom := by
    apply (cancel_mono L.isoHomologyι₀.inv).mp
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h.symm
  rw [he]
  infer_instance

/--
For an additively aspherical augmentation, the sequence from normalized degree one
to normalized degree zero to the augmentation target is exact on elements, and its
augmentation map is surjective.
-/
theorem augmentation_zero_exact_epi_of_quasiIso :
    Function.Exact ((normalized P).d 1 0).hom ((augmentation P).f 0).hom ∧
      Function.Surjective ((augmentation P).f 0).hom := by
  let K := normalized P
  let L := (ChainComplex.single₀ (ModuleCat.{v} R)).obj P.right
  let π := (augmentation P).f 0
  have hπ : K.d 1 0 ≫ π = 0 :=
    ((ChainComplex.toSingle₀Equiv K P.right) (augmentation P)).property
  let e := L.pOpcyclesIso 1 0 (by simp) (by rfl)
  letI : IsIso (HomologicalComplex.opcyclesMap (augmentation P) 0) :=
    augmentation_opcyclesMap_isIso P
  have hd : K.descOpcycles π 1 (by simp) hπ =
      HomologicalComplex.opcyclesMap (augmentation P) 0 ≫ e.inv := by
    apply (cancel_epi (K.pOpcycles 0)).mp
    rw [K.p_descOpcycles, ← Category.assoc, HomologicalComplex.p_opcyclesMap,
      Category.assoc]
    change π = π ≫ (e.hom ≫ e.inv)
    rw [Iso.hom_inv_id, Category.comp_id]
  haveI : IsIso (K.descOpcycles π 1 (by simp) hπ) := by rw [hd]; infer_instance
  have h := (ChainComplex.isIso_descOpcycles_iff K π hπ).mp inferInstance
  exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h.1,
    (ModuleCat.epi_iff_surjective π).mp h.2⟩

/--
If the normalized augmentation is a quasi-isomorphism, the degree-zero simplicial
module augmentation `P₀ → M` is surjective.
-/
theorem original_augmentation_zero_surjective_of_quasiIso :
    Function.Surjective (P.hom.app (op ⦋0⦌)).hom := by
  intro a
  obtain ⟨x, hx⟩ := (augmentation_zero_exact_epi_of_quasiIso P).2 a
  refine ⟨((inclusionOfMooreComplexMap P.left).f 0).hom x, ?_⟩
  have h := (congrArg (fun f => f.hom x) (augmentation_zero P)).symm.trans hx
  exact h

/--
The normalized complex of an additively aspherical augmentation is exact at every
positive degree `n + 1`.
-/
theorem normalized_exactAt_positive_of_quasiIso (n : ℕ) :
    (normalized P).ExactAt (n + 1) :=
  (quasiIsoAt_iff_exactAt' (augmentation P) (n + 1)
    (ChainComplex.exactAt_succ_single_obj P.right n)).mp inferInstance

/--
Every cycle `x` in normalized degree `n + 1` is the differential of an element in
normalized degree `n + 2`, under additive asphericity of the augmentation.
-/
theorem normalized_cycle_boundary_of_quasiIso (n : ℕ)
    (x : (normalized P).X (n + 1)) (hx : ((normalized P).d (n + 1) n).hom x = 0) :
    ∃ y : (normalized P).X (n + 2), ((normalized P).d (n + 2) (n + 1)).hom y = x := by
  have h := normalized_exactAt_positive_of_quasiIso P n
  have hs := ((normalized P).exactAt_iff' (i := n + 2) (j := n + 1) (k := n)
    (by simp) (by simp)).mp h
  exact ((ShortComplex.moduleCat_exact_iff _).mp hs) x hx

/--
If `x ∈ P₀` has augmentation zero, there is `y ∈ P₁` with `d₀ y = x`,
`d₁ y = 0`, and augmentation zero, assuming the normalized augmentation is a
quasi-isomorphism.
-/
theorem original_zero_obstruction_filler_of_quasiIso
    (x : P.left.obj (op ⦋0⦌)) (hx : (P.hom.app (op ⦋0⦌)).hom x = 0) :
    ∃ y : P.left.obj (op ⦋1⦌),
      (P.left.δ (0 : Fin 2)).hom y = x ∧
        (P.left.δ (1 : Fin 2)).hom y = 0 ∧ (P.hom.app (op ⦋1⦌)).hom y = 0 := by
  let x' := (termEquiv P.left 0).symm ⟨x, Submodule.mem_top⟩
  have hπ : ((augmentation P).f 0).hom x' = 0 := by
    rw [augmentation_zero]
    change (P.hom.app (op ⦋0⦌)).hom
      (((inclusionOfMooreComplexMap P.left).f 0).hom x') = 0
    rw [termEquiv_symm_value]
    exact hx
  obtain ⟨y', hy⟩ := ((augmentation_zero_exact_epi_of_quasiIso P).1 x').mp hπ
  let y := termEquiv P.left 1 y'
  have hnorm : (P.left.δ (1 : Fin 2)).hom y.val = 0 :=
    (mem_normalizedSubmodule P.left 0 y.val).mp y.property 0
  have hzero : (P.left.δ (0 : Fin 2)).hom y.val = x := by
    have h := termEquiv_d_value P.left 0 y'
    rw [hy, LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have hpoint : (P.hom.app (op ⦋1⦌)).hom y.val = 0 := by
    have h := congrArg (fun h => h.hom y.val)
      (P.hom.naturality (SimplexCategory.δ (1 : Fin 2)).op)
    change (P.hom.app (op ⦋0⦌)).hom ((P.left.δ (1 : Fin 2)).hom y.val) =
      (P.hom.app (op ⦋1⦌)).hom y.val at h
    rw [hnorm, map_zero] at h
    exact h.symm
  exact ⟨y.val, hzero, hnorm, hpoint⟩

/--
If `x ∈ P_(n+1)` has every face zero, there is `y ∈ P_(n+2)` with `d₀ y = x`,
all other faces zero, and augmentation zero, under additive asphericity.
-/
theorem original_positive_obstruction_filler_of_quasiIso (n : ℕ)
    (x : P.left.obj (op ⦋n + 1⦌))
    (hx : ∀ j : Fin (n + 2), (P.left.δ j).hom x = 0) :
    ∃ y : P.left.obj (op ⦋n + 2⦌),
      (P.left.δ (0 : Fin (n + 3))).hom y = x ∧
        (∀ j : Fin (n + 2), (P.left.δ j.succ).hom y = 0) ∧
          (P.hom.app (op ⦋n + 2⦌)).hom y = 0 := by
  let xN : normalizedSubmodule P.left (n + 1) :=
    ⟨x, (mem_normalizedSubmodule P.left n x).mpr (fun j => hx j.succ)⟩
  let x' := (termEquiv P.left (n + 1)).symm xN
  have hcycle : ((normalized P).d (n + 1) n).hom x' = 0 := by
    apply (termEquiv P.left n).injective
    apply Subtype.ext
    rw [termEquiv_d_value, map_zero, LinearEquiv.apply_symm_apply]
    exact hx 0
  obtain ⟨y', hy⟩ := normalized_cycle_boundary_of_quasiIso P n x' hcycle
  let y := termEquiv P.left (n + 2) y'
  have hnorm : ∀ j : Fin (n + 2), (P.left.δ j.succ).hom y.val = 0 :=
    (mem_normalizedSubmodule P.left (n + 1) y.val).mp y.property
  have hzero : (P.left.δ (0 : Fin (n + 3))).hom y.val = x := by
    have h := termEquiv_d_value P.left (n + 1) y'
    rw [hy, LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have hpoint : (P.hom.app (op ⦋n + 2⦌)).hom y.val = 0 := by
    have h := congrArg (fun h => h.hom y.val)
      (P.hom.naturality (SimplexCategory.δ (1 : Fin (n + 3))).op)
    change (P.hom.app (op ⦋n + 1⦌)).hom ((P.left.δ (1 : Fin (n + 3))).hom y.val) =
      (P.hom.app (op ⦋n + 2⦌)).hom y.val at h
    have hz := hnorm (0 : Fin (n + 2))
    change (P.left.δ (1 : Fin (n + 3))).hom y.val = 0 at hz
    exact h.symm.trans ((congrArg (P.hom.app (op ⦋n + 1⦌)).hom hz).trans (map_zero _))
  exact ⟨y.val, hzero, hnorm, hpoint⟩

end AlgebraicTopology.ModuleResolutionAsphericity

end
