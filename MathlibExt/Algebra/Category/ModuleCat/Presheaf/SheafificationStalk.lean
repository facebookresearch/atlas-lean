/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

/-
Historical source credit: @junekim623, Muse
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Topology.Sheaves.Sheafify

/-!
# Stalk comparison for module sheafification

Let R be a sheaf of rings on a topological space X, and assume the stated weak sheafification
and locally bijective characterization for additive presheaves. For an R-module presheaf M,
its sheafification unit u : M → aM induces an isomorphism on every stalk, linear over the
stalk ring R_x.

The comparison defined here is aM_x ≃_{R_x} M_x; its inverse is the stalk map of u. On a germ
of a section s, that inverse sends germ_M(s) to germ_aM(u(s)). For a module-presheaf morphism
φ, the induced stalk map is R_x-linear and sends germ(s) to germ(φ(s)).

Mathlib presheaf-of-modules sheafification and stalk APIs (J. Riou, A. Yang).
-/

open _root_.CategoryTheory CategoryTheory _root_.TopCat TopCat

@[expose] public section

universe u

variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (M : PresheafOfModules.{u} R.obj) (x : X)

namespace PresheafOfModules

section StalkEquiv


/-- The linear comparison from a sheafified stalk to the presheaf stalk.

At x ∈ X, the stalk of aM is linearly equivalent over R_x to the stalk of M. The inverse
equivalence is induced by the sheafification unit. -/
noncomputable def sheafificationStalkLinearEquiv :
    ↥(TopCat.Presheaf.stalk
        ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj M).val.presheaf x)
      ≃ₗ[↥(TopCat.Presheaf.stalk R.obj x)]
        ↥(TopCat.Presheaf.stalk M.presheaf x) := by
  -- MODULE adjunction unit; use `u` throughout, never a raw `φ`.
  set u := ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app M) with hu
  let N : PresheafOfModules.{u} R.obj :=
    ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj M).val
  -- Additive stalk map along the unit; the codomain is definitionally the stalk
  -- of the bundled module sheafification presheaf, so its `Module` instance is retained.
  set ψ : ↥(TopCat.Presheaf.stalk M.presheaf x) →+
      ↥(TopCat.Presheaf.stalk N.presheaf x) :=
    ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf R.obj).map u)) with hψ
  -- Sectionwise scalar compatibility from `map_smul (u.app U)`; the scalar hom is identity.
  have hlin : ∀ (U : (TopologicalSpace.Opens X)ᵒᵖ) (r : R.obj.obj U) (m : M.obj U),
      ((u.app U).hom (r • m) : N.obj U) = r • ((u.app U).hom m : N.obj U) := by
    intro U r m
    have h := (u.app U).hom.map_smul r m
    simp only [h]
  have hmap_smul : ∀ (r : ↥(TopCat.Presheaf.stalk R.obj x))
      (m : ↥(TopCat.Presheaf.stalk M.presheaf x)),
      ψ (r • m) = r • ψ m := by
    intro r m
    obtain ⟨U, hU, r₀, hr₀⟩ := TopCat.Presheaf.exists_germ_eq R.obj r
    obtain ⟨V, hV, hm, m₀, hm₀⟩ :=
      TopCat.Presheaf.exists_le_germ_eq M.presheaf m hU
    rw [← hr₀, ← hm₀]
    -- Reduce to germs over the common open `V`.
    have hr : TopCat.Presheaf.germ R.obj U x hU r₀ =
        TopCat.Presheaf.germ R.obj V x hm (R.obj.map (homOfLE hV).op r₀) := by
      rw [TopCat.Presheaf.germ_res_apply]
    rw [hr]
    -- Stalk map on germs is the germ of the section map, by rfl on the
    -- bundled module morphism (never raw sheafify).
    have hgerm : ∀ (s : M.obj (Opposite.op V)),
        ψ (TopCat.Presheaf.germ M.presheaf V x hm s) =
          TopCat.Presheaf.germ N.presheaf V x hm ((u.app (Opposite.op V)).hom s) := by
      intro s
      rw [hψ]
      exact TopCat.Presheaf.stalkFunctor_map_germ_apply'
        (f := (PresheafOfModules.toPresheaf R.obj).map u) V x hm s
    -- Use the original germ scalar laws at the actual common-open sections.
    let a : R.obj.obj (Opposite.op V) := R.obj.map (homOfLE hV).op r₀
    let b : M.obj (Opposite.op V) := m₀
    have hM := PresheafOfModules.germ_ringCat_smul M x V hm a b
    have hN := PresheafOfModules.germ_ringCat_smul N x V hm a
      ((u.app (Opposite.op V)).hom b)
    calc
      ψ (TopCat.Presheaf.germ R.obj V x hm a • TopCat.Presheaf.germ M.presheaf V x hm b) =
          ψ (TopCat.Presheaf.germ M.presheaf V x hm (a • b)) := congrArg ψ hM.symm
      _ = TopCat.Presheaf.germ N.presheaf V x hm
          ((u.app (Opposite.op V)).hom (a • b)) := hgerm (a • b)
      _ = TopCat.Presheaf.germ N.presheaf V x hm
          (a • (u.app (Opposite.op V)).hom b) :=
        congrArg (fun t => TopCat.Presheaf.germ N.presheaf V x hm t)
          (hlin (Opposite.op V) a b)
      _ = TopCat.Presheaf.germ R.obj V x hm a • TopCat.Presheaf.germ N.presheaf V x hm
          ((u.app (Opposite.op V)).hom b) := hN
      _ = TopCat.Presheaf.germ R.obj V x hm a • ψ (TopCat.Presheaf.germ M.presheaf V x hm b) :=
        congrArg (fun t => TopCat.Presheaf.germ R.obj V x hm a • t) (hgerm b).symm
  let L : ↥(TopCat.Presheaf.stalk M.presheaf x) →ₗ[↥(TopCat.Presheaf.stalk R.obj x)]
      ↥(TopCat.Presheaf.stalk N.presheaf x) :=
    { toFun := ψ
      map_add' := fun a b => map_add _ a b
      map_smul' := hmap_smul }
  -- Identify the mapped morphism with the sheafify unit, without retyping the codomain.
  have hmor : (PresheafOfModules.toPresheaf R.obj).map u =
      CategoryTheory.toSheafify (Opens.grothendieckTopology X) M.presheaf := by
    rw [hu]
    exact PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app _ _
  have hiso : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf R.obj).map u)) := by
    rw [hmor]
    exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
      M.presheaf
  have hbij : Function.Bijective ψ := by
    rw [hψ]
    exact ConcreteCategory.bijective_of_isIso _
  have hbijL : Function.Bijective L := hbij
  exact (LinearEquiv.ofBijective L hbijL).symm

end StalkEquiv

end PresheafOfModules

namespace PresheafOfModules

section StalkMapLinearSection

variable {R : X.Presheaf RingCat.{u}}

/-- The linear stalk map of a module-presheaf morphism.

For a ring presheaf R and φ : M → N, the induced map M_x → N_x is a morphism of modules over
the stalk ring R_x. -/
noncomputable def stalkMapLinear {M N : PresheafOfModules.{u} R} (φ : M ⟶ N)
    (x : X) :
    ModuleCat.of ↥(R.stalk x) ↥(TopCat.Presheaf.stalk M.presheaf x) ⟶
      ModuleCat.of ↥(R.stalk x) ↥(TopCat.Presheaf.stalk N.presheaf x) := by
  set ψ : ↥(TopCat.Presheaf.stalk M.presheaf x) →+
      ↥(TopCat.Presheaf.stalk N.presheaf x) :=
    ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((PresheafOfModules.toPresheaf R).map φ)) with hψ
  have hgerm : ∀ (V : TopologicalSpace.Opens X) (hxV : x ∈ V)
      (s : M.obj (Opposite.op V)),
      ψ (TopCat.Presheaf.germ M.presheaf V x hxV s) =
        TopCat.Presheaf.germ N.presheaf V x hxV
          ((φ.app (Opposite.op V)).hom s) := by
    intro V hxV s
    rw [hψ]
    exact TopCat.Presheaf.stalkFunctor_map_germ_apply'
      (f := (PresheafOfModules.toPresheaf R).map φ) V x hxV s
  have hmap_smul : ∀ (r : ↥(TopCat.Presheaf.stalk R x))
      (m : ↥(TopCat.Presheaf.stalk M.presheaf x)),
      ψ (r • m) = r • ψ m := by
    intro r m
    obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
    obtain ⟨V, hVU, hxV, a, rfl⟩ :=
      TopCat.Presheaf.exists_le_germ_eq R r hxU
    have hsV : TopCat.Presheaf.germ M.presheaf U x hxU s =
        TopCat.Presheaf.germ M.presheaf V x hxV
          (M.presheaf.map (homOfLE hVU).op s) :=
      (TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE hVU) x hxV s).symm
    rw [hsV]
    let b : M.obj (Opposite.op V) := M.presheaf.map (homOfLE hVU).op s
    have hM := PresheafOfModules.germ_ringCat_smul M x V hxV a b
    have hN := PresheafOfModules.germ_ringCat_smul N x V hxV a
      ((φ.app (Opposite.op V)).hom b)
    calc
      ψ (R.germ V x hxV a • TopCat.Presheaf.germ M.presheaf V x hxV b) =
          ψ (TopCat.Presheaf.germ M.presheaf V x hxV (a • b)) := congrArg ψ hM.symm
      _ = TopCat.Presheaf.germ N.presheaf V x hxV
          ((φ.app (Opposite.op V)).hom (a • b)) := hgerm V hxV (a • b)
      _ = TopCat.Presheaf.germ N.presheaf V x hxV
          (a • (φ.app (Opposite.op V)).hom b) :=
        congrArg (fun t => TopCat.Presheaf.germ N.presheaf V x hxV t)
          ((φ.app (Opposite.op V)).hom.map_smul a b)
      _ = R.germ V x hxV a • TopCat.Presheaf.germ N.presheaf V x hxV
          ((φ.app (Opposite.op V)).hom b) := hN
      _ = R.germ V x hxV a • ψ (TopCat.Presheaf.germ M.presheaf V x hxV b) :=
        congrArg (fun t => R.germ V x hxV a • t) (hgerm V hxV b).symm
  exact ModuleCat.ofHom
    { toFun := ψ
      map_add' := fun a b => map_add _ a b
      map_smul' := hmap_smul }

end StalkMapLinearSection

section StalkMapLinearGermSection

variable (R : X.Presheaf RingCat.{u})

omit [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] in
omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The linear stalk map on a section germ.

For x ∈ V and s ∈ M(V), φ_x(germ_M(s)) = germ_N(φ_V(s)). -/
theorem stalkMapLinear_germ {M N : PresheafOfModules.{u} R} (φ : M ⟶ N)
    (x : X) (V : TopologicalSpace.Opens X) (hxV : x ∈ V) (s : M.obj (Opposite.op V)) :
    (stalkMapLinear φ x) (TopCat.Presheaf.germ M.presheaf V x hxV s)
      = TopCat.Presheaf.germ N.presheaf V x hxV
          ((φ.app (Opposite.op V)) s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply' V x hxV
    ((_root_.PresheafOfModules.toPresheaf R).map φ) s

end StalkMapLinearGermSection

section SheafificationSymmSection

/-- The inverse stalk comparison is the sheafification-unit map.

For m ∈ M_x, the inverse of aM_x ≃ M_x sends m to its image under the linear stalk map of M →
aM. -/
theorem sheafificationStalkLinearEquiv_symm_apply (M : PresheafOfModules.{u} R.obj)
    (x : X) (m : ↥(TopCat.Presheaf.stalk M.presheaf x)) :
    (PresheafOfModules.sheafificationStalkLinearEquiv R M x).symm m =
      PresheafOfModules.stalkMapLinear
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app M) x m := by
  obtain ⟨V, hxV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
  have hL : (PresheafOfModules.sheafificationStalkLinearEquiv R M x).symm
        (TopCat.Presheaf.germ M.presheaf V x hxV s) =
        TopCat.Presheaf.germ
          ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj M).val.presheaf
          V x hxV
          (((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app M).app
            (Opposite.op V) s) := by
    unfold PresheafOfModules.sheafificationStalkLinearEquiv
    simp only [LinearEquiv.symm_symm, LinearEquiv.ofBijective_apply]
    exact TopCat.Presheaf.stalkFunctor_map_germ_apply' V x hxV
      ((PresheafOfModules.toPresheaf R.obj).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app M)) s
  have hrhs := PresheafOfModules.stalkMapLinear_germ R.obj
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app M) x V hxV s
  exact hL.trans hrhs.symm

/-- The inverse sheafification comparison on germs.

For a section s over an open neighborhood V of x, the inverse stalk comparison sends germ_M(s)
to the germ in aM of the unit image of s. -/
theorem sheafificationStalkLinearEquiv_symm_germ (M : PresheafOfModules.{u} R.obj)
    (x : X) (V : TopologicalSpace.Opens X) (hxV : x ∈ V)
    (s : M.obj (Opposite.op V)) :
    (PresheafOfModules.sheafificationStalkLinearEquiv R M x).symm
        (TopCat.Presheaf.germ M.presheaf V x hxV s) =
      TopCat.Presheaf.germ
        ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj M).val.presheaf
        V x hxV
        (((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app M).app
          (Opposite.op V) s) := by
  have hbase := sheafificationStalkLinearEquiv_symm_apply R M x
    (TopCat.Presheaf.germ M.presheaf V x hxV s)
  have hrhs := PresheafOfModules.stalkMapLinear_germ R.obj
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app M) x V hxV s
  exact hbase.trans hrhs

end SheafificationSymmSection

end PresheafOfModules

end
