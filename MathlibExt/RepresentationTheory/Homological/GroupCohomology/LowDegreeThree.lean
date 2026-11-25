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

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Explicit degree-three group cohomology

This file extends the low-degree inhomogeneous group-cohomology API to
degree three.  It supplies explicit degree-three cochains, cocycles,
coboundaries, the `d₃₄` formula, and the quotient map `H3π` into the existing
abstract `groupCohomology A 3`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Representation

universe u

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]
variable (A : Rep k G)

/-- Coordinate equivalence for three group variables. -/
def finThreeEquiv : (Fin 3 → G) ≃ G × G × G :=
  (Fin.consEquiv _).symm.trans
    ((Equiv.refl G).prodCongr (piFinTwoEquiv fun _ => G))

/-- Coordinate equivalence for four group variables. -/
def finFourEquiv : (Fin 4 → G) ≃ G × G × G × G :=
  (Fin.consEquiv _).symm.trans
    ((Equiv.refl G).prodCongr (finThreeEquiv (G := G)))

/-- The fourth inhomogeneous cochain object in explicit coordinates. -/
def cochainsIso₄ : (inhomogeneousCochains A).X 4 ≅
    ModuleCat.of k (G × G × G × G → A) :=
  (LinearEquiv.funCongrLeft k A (finFourEquiv (G := G))).toModuleIso.symm

/-- The degree-three inhomogeneous differential. -/
@[simps!]
def d₃₄ : ModuleCat.of k (G × G × G → A) ⟶
    ModuleCat.of k (G × G × G × G → A) :=
  ModuleCat.ofHom
  { toFun := fun f g =>
      A.ρ g.1 (f (g.2.1, g.2.2.1, g.2.2.2)) -
        f (g.1 * g.2.1, g.2.2.1, g.2.2.2) +
        f (g.1, g.2.1 * g.2.2.1, g.2.2.2) -
        f (g.1, g.2.1, g.2.2.1 * g.2.2.2) +
        f (g.1, g.2.1, g.2.2.1)
    map_add' := fun x y => funext fun g => by
      dsimp
      rw [map_add]
      abel
    map_smul' := fun r x => funext fun g => by
      dsimp
      simp only [map_smul, smul_add, smul_sub] }

/-- The explicit `d₃₄` is the degree-three differential of the abstract
inhomogeneous cochain complex in coordinates. -/
theorem comp_d₃₄_eq :
    (cochainsIso₃ A).hom ≫ d₃₄ A =
      (inhomogeneousCochains A).d 3 4 ≫ (cochainsIso₄ A).hom := by
  ext x y
  let v : Fin 4 → G := (finFourEquiv (G := G)).symm y
  have htail : (fun i : Fin 3 =>
      (Fin.cons y.2.1
        (Fin.cons y.2.2.1
          (Fin.cons y.2.2.2 (finZeroElim : Fin 0 → G))) : Fin 3 → G) i) =
      (finThreeEquiv (G := G)).symm y.2 := by
    funext i
    fin_cases i <;> rfl
  have h0 : Fin.contractNth 0 (fun a b : G => a * b) v =
      (finThreeEquiv (G := G)).symm
        (y.1 * y.2.1, y.2.2.1, y.2.2.2) := by
    funext i
    fin_cases i <;> rfl
  have h1 : Fin.contractNth 1 (fun a b : G => a * b) v =
      (finThreeEquiv (G := G)).symm
        (y.1, y.2.1 * y.2.2.1, y.2.2.2) := by
    funext i
    fin_cases i <;> rfl
  have h2 : Fin.contractNth 2 (fun a b : G => a * b) v =
      (finThreeEquiv (G := G)).symm
        (y.1, y.2.1, y.2.2.1 * y.2.2.2) := by
    funext i
    fin_cases i <;> rfl
  have h3 : Fin.contractNth 3 (fun a b : G => a * b) v =
      (finThreeEquiv (G := G)).symm
        (y.1, y.2.1, y.2.2.1) := by
    funext i
    fin_cases i <;> rfl
  change A.ρ y.1 (x _) - x _ + x _ - x _ + x _ = _ + _
  dsimp [cochainsIso₄, finFourEquiv, finThreeEquiv]
  rw [Fin.sum_univ_four]
  norm_num [sub_eq_add_neg]
  change _ = A.ρ y.1
      (x (fun i : Fin 3 =>
        (Fin.cons y.2.1
          (Fin.cons y.2.2.1
            (Fin.cons y.2.2.2 (finZeroElim : Fin 0 → G))) : Fin 3 → G) i)) +
      (-x (Fin.contractNth 0 (fun a b : G => a * b) v) +
        x (Fin.contractNth 1 (fun a b : G => a * b) v) +
        -x (Fin.contractNth 2 (fun a b : G => a * b) v) +
        x (Fin.contractNth 3 (fun a b : G => a * b) v))
  rw [htail, h0, h1, h2, h3]
  abel

@[reassoc, elementwise]
theorem eq_d₃₄_comp_inv :
    (cochainsIso₃ A).inv ≫ (inhomogeneousCochains A).d 3 4 =
      d₃₄ A ≫ (cochainsIso₄ A).inv :=
  (CommSq.horiz_inv ⟨comp_d₃₄_eq A⟩).w

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem d₂₃_comp_d₃₄ : d₂₃ A ≫ d₃₄ A = 0 := by
  ext f g
  simp [d₂₃, d₃₄, mul_assoc, Pi.zero_apply (M := fun _ => A)]
  abel

open ShortComplex

/-- Explicit short complex computing degree-three cohomology. -/
@[simps! -isSimp f g]
def shortComplexH3 : ShortComplex (ModuleCat k) :=
  mk (d₂₃ A) (d₃₄ A) (d₂₃_comp_d₃₄ A)

/-- Explicit degree-three cocycles. -/
def cocycles₃ : Submodule k (G × G × G → A) :=
  LinearMap.ker (d₃₄ A).hom

/-- Explicit degree-three coboundaries. -/
def coboundaries₃ : Submodule k (G × G × G → A) :=
  LinearMap.range (d₂₃ A).hom

variable {A}

@[macro_inline]
instance : FunLike (cocycles₃ A) (G × G × G) A :=
  ⟨Subtype.val, Subtype.val_injective⟩

@[simp]
theorem cocycles₃.coe_mk (f : G × G × G → A) (hf) :
    ((⟨f, hf⟩ : cocycles₃ A) : G × G × G → A) = f := rfl

@[simp]
theorem cocycles₃.val_eq_coe (f : cocycles₃ A) : f.1 = f := rfl

@[ext]
theorem cocycles₃_ext {f₁ f₂ : cocycles₃ A}
    (hEq : ∀ g h j : G, f₁ (g, h, j) = f₂ (g, h, j)) : f₁ = f₂ :=
  DFunLike.ext f₁ f₂ fun p => hEq p.1 p.2.1 p.2.2

theorem mem_cocycles₃_def (f : G × G × G → A) :
    f ∈ cocycles₃ A ↔ ∀ g h i j : G,
      A.ρ g (f (h, i, j)) - f (g * h, i, j) +
        f (g, h * i, j) - f (g, h, i * j) + f (g, h, i) = 0 :=
  LinearMap.mem_ker.trans <| by
    simp_rw [funext_iff, d₃₄_hom_apply, Prod.forall]
    rfl

theorem d₂₃_apply_mem_cocycles₃ (x : G × G → A) :
    d₂₃ A x ∈ cocycles₃ A :=
  d₂₃_comp_d₃₄_apply _ _

@[simp]
theorem cocycles₃.d₃₄_apply (x : cocycles₃ A) : d₃₄ A x = 0 := x.2

@[macro_inline]
instance : FunLike (coboundaries₃ A) (G × G × G) A :=
  ⟨Subtype.val, Subtype.val_injective⟩

@[simp]
theorem coboundaries₃.coe_mk (f : G × G × G → A) (hf) :
    ((⟨f, hf⟩ : coboundaries₃ A) : G × G × G → A) = f := rfl

@[simp]
theorem coboundaries₃.val_eq_coe (f : coboundaries₃ A) : f.1 = f := rfl

@[ext]
theorem coboundaries₃_ext {f₁ f₂ : coboundaries₃ A}
    (hEq : ∀ g h j : G, f₁ (g, h, j) = f₂ (g, h, j)) : f₁ = f₂ :=
  DFunLike.ext f₁ f₂ fun p => hEq p.1 p.2.1 p.2.2

lemma coboundaries₃_le_cocycles₃ (A : Rep k G) :
    coboundaries₃ A ≤ cocycles₃ A := by
  rintro _ ⟨x, rfl⟩
  exact d₂₃_apply_mem_cocycles₃ x

/-- Natural inclusion from explicit three-coboundaries to three-cocycles. -/
abbrev coboundariesToCocycles₃ (A : Rep k G) :
    coboundaries₃ A →ₗ[k] cocycles₃ A :=
  Submodule.inclusion (coboundaries₃_le_cocycles₃ A)

variable (A)

set_option backward.isDefEq.respectTransparency.types false in
/-- The explicit degree-three short complex is isomorphic to the abstract
degree-three short complex of inhomogeneous cochains. -/
@[simps! hom inv]
def isoShortComplexH3 :
    (inhomogeneousCochains A).sc 3 ≅ shortComplexH3 A :=
  (inhomogeneousCochains A).isoSc' 2 3 4 (by simp) (by simp) ≪≫
    isoMk (cochainsIso₂ A) (cochainsIso₃ A) (cochainsIso₄ A)
      (comp_d₂₃_eq A) (comp_d₃₄_eq A)

/-- Abstract cycles in degree three are isomorphic to explicit
inhomogeneous three-cocycles. -/
def isoCocycles₃ : cocycles A 3 ≅ ModuleCat.of k (cocycles₃ A) :=
  cyclesMapIso' (isoShortComplexH3 A) _
    (shortComplexH3 A).moduleCatLeftHomologyData

/-- Shorthand for third group cohomology. -/
abbrev H3 := groupCohomology A 3

/-- Quotient map from explicit degree-three cocycles to third group
cohomology. -/
def H3π : ModuleCat.of k (cocycles₃ A) ⟶ H3 A :=
  (isoCocycles₃ A).inv ≫ π A 3

set_option backward.isDefEq.respectTransparency false in
instance : Epi (H3π A) := inferInstanceAs <| Epi (_ ≫ _)

variable {A}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem H3π_eq_zero_iff (x : cocycles₃ A) :
    H3π A x = 0 ↔ (x : G × G × G → A) ∈ coboundaries₃ A := by
  have h := leftHomologyπ_naturality'_assoc (isoShortComplexH3 A).inv
    (shortComplexH3 A).moduleCatLeftHomologyData (leftHomologyData _)
    ((inhomogeneousCochains A).sc 3).leftHomologyIso.hom
  simp only [H3π, isoCocycles₃, π, HomologicalComplex.homologyπ,
    homologyπ, cyclesMapIso'_inv, leftHomologyπ, ← h,
    ← leftHomologyMapIso'_inv, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply, map_eq_zero_iff _
      ((ModuleCat.mono_iff_injective <| _).1 inferInstance)]
  simp [LinearMap.range_codRestrict, coboundaries₃, shortComplexH3,
    cocycles₃]

theorem H3π_eq_iff (x y : cocycles₃ A) :
    H3π A x = H3π A y ↔
      (x : G × G × G → A) - y ∈ coboundaries₃ A := by
  rw [← sub_eq_zero, ← map_sub, H3π_eq_zero_iff]
  rfl

@[elab_as_elim]
theorem H3_induction_on {C : H3 A → Prop} (x : H3 A)
    (h : ∀ z : cocycles₃ A, C (H3π A z)) : C x :=
  groupCohomology_induction_on x fun y => by
    simpa [H3π] using h ((isoCocycles₃ A).hom y)

end groupCohomology
