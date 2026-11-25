/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.ModuleCat.RingHomInduction.Composition

/-!
# Identity and associativity of induction

The unit-tensor formulas for induction comparisons prove their identity and associativity
coherence with functor unitors and associators. The statements concern the existing identity and
composition isomorphisms.
-/

@[expose] public section

open CategoryTheory

universe u v s t w

namespace ModuleCat.RingHomInduction

section IdentityCoherence

variable {k : Type u} {R : Type v} [Ring k] [Ring R] (φ : k →+* R)


/-- Composition with identity induction agrees with the left unitor comparison. -/
theorem composition_left_identity :
    (compositionIso.{u, u, v, max u v w} (RingHom.id k) φ).hom ≫
        (congrIso.{u, v, max u v w} (RingHom.comp_id φ)).hom =
      Functor.whiskerRight (identityIso.{u, max u v w} k).hom (ModuleCat.induceScalars.{u, v, max u v w} φ) ≫
        (ModuleCat.induceScalars.{u, v, max u v w} φ).leftUnitor.hom := by
  apply NatTrans.ext
  funext M
  apply composition_hom_ext.{u, u, v, max u v w} (RingHom.id k) φ M ((ModuleCat.induceScalars.{u, v, max u v w} φ).obj
    M)
  intro m
  let K : ModuleCat.{max u v w} k := (ModuleCat.induceScalars.{u, u, max u v w} (RingHom.id k)).obj M
  let N : ModuleCat.{max u v w} R := (ModuleCat.induceScalars.{u, v, max u v w} φ).obj M
  let y : K := tensor (RingHom.id k) M 1 m
  let z : (ModuleCat.induceScalars.{u, v, max u v w} φ).obj K := tensor φ K 1 y
  let i : K ⟶ M := (identityIso.{u, max u v w} k).hom.app M
  have hi : i y = m := (identityIso_hom_tensor.{u, max u v w} k M 1 m).trans (one_smul k m)
  have hmap : (ModuleCat.induceScalars.{u, v, max u v w} φ).map i z = (show N from tensor φ M 1 (i y)) := by
    exact ModuleCat.induceScalars_map_tensor.{u, v, max u v w} φ i 1 y
  have hr : (ModuleCat.induceScalars.{u, v, max u v w} φ).map i z = (show N from tensor φ M 1 m) :=
    hmap.trans (congrArg (fun a : M => (show N from tensor φ M 1 a)) hi)
  have hμ := compositionIso_hom_unit.{u, u, v, max u v w} (RingHom.id k) φ M m
  have hν := congrIso_hom_unit.{u, v, max u v w} (RingHom.comp_id φ) M m
  have hl : (congrIso.{u, v, max u v w} (RingHom.comp_id φ)).hom.app M
      ((compositionIso.{u, u, v, max u v w} (RingHom.id k) φ).hom.app M z) =
      (show N from tensor φ M 1 m) :=
    (congrArg ((congrIso.{u, v, max u v w} (RingHom.comp_id φ)).hom.app M) hμ).trans hν
  exact hl.trans hr.symm

/-- Composition with target identity induction agrees with the right unitor comparison. -/
theorem composition_right_identity :
    (compositionIso.{u, v, v, max u v w} φ (RingHom.id R)).hom ≫
        (congrIso.{u, v, max u v w} (RingHom.id_comp φ)).hom =
      Functor.whiskerLeft (ModuleCat.induceScalars.{u, v, max u v w} φ) (identityIso.{v, max u v w} R).hom ≫
        (ModuleCat.induceScalars.{u, v, max u v w} φ).rightUnitor.hom := by
  apply NatTrans.ext
  funext M
  apply composition_hom_ext.{u, v, v, max u v w} φ (RingHom.id R) M ((ModuleCat.induceScalars.{u, v, max u v w} φ).obj
    M)
  intro m
  let K : ModuleCat.{max u v w} R := (ModuleCat.induceScalars.{u, v, max u v w} φ).obj M
  let y : K := tensor φ M 1 m
  let z : (ModuleCat.induceScalars.{v, v, max u v w} (RingHom.id R)).obj K :=
    tensor (RingHom.id R) K 1 y
  have hr : (identityIso.{v, max u v w} R).hom.app K z = y :=
    (identityIso_hom_tensor.{v, max u v w} R K 1 y).trans (one_smul R y)
  have hμ := compositionIso_hom_unit.{u, v, v, max u v w} φ (RingHom.id R) M m
  have hν := congrIso_hom_unit.{u, v, max u v w} (RingHom.id_comp φ) M m
  have hl : (congrIso.{u, v, max u v w} (RingHom.id_comp φ)).hom.app M
      ((compositionIso.{u, v, v, max u v w} φ (RingHom.id R)).hom.app M z) = y :=
    (congrArg ((congrIso.{u, v, max u v w} (RingHom.id_comp φ)).hom.app M) hμ).trans hν
  exact hl.trans hr.symm

end IdentityCoherence

section Associativity

variable {k : Type u} {R : Type v} {S : Type s} {T : Type t}
  [Ring k] [Ring R] [Ring S] [Ring T]
  (φ : k →+* R) (ψ : R →+* S) (χ : S →+* T)


/-- The adjunction for threefold induction is the composite adjunction. -/
noncomputable def tripleAdj : ((ModuleCat.induceScalars.{u, v, max u v s t w} φ) ⋙ (ModuleCat.induceScalars.{v, s, max
  u v s t w} ψ)) ⋙ (ModuleCat.induceScalars.{s, t, max u v s t w} χ) ⊣ (ModuleCat.restrictScalars.{max u v s t w} χ) ⋙
  (ModuleCat.restrictScalars.{max u v s t w} ψ) ⋙ (ModuleCat.restrictScalars.{max u v s t w} φ) :=
  ((ModuleCat.induceRestrictScalarsAdj.{u, v, max u v s t w} φ).comp (ModuleCat.induceRestrictScalarsAdj.{v, s, max u
  v s t w} ψ)).comp (ModuleCat.induceRestrictScalarsAdj.{s, t, max u v s t w} χ)

theorem tripleAdj_hom_apply (M : ModuleCat.{max u v s t w} k)
    (N : ModuleCat.{max u v s t w} T) (f : (((ModuleCat.induceScalars.{u, v, max u v s t w} φ) ⋙
      (ModuleCat.induceScalars.{v, s, max u v s t w} ψ)) ⋙ (ModuleCat.induceScalars.{s, t, max u v s t w} χ)).obj M ⟶
      N) (m : M) :
    (tripleAdj.{u, v, s, t, w} φ ψ χ).homEquiv M N f m =
      f (tensor χ (Carrier ψ (Carrier φ M)) 1
        (tensor ψ (Carrier φ M) 1 (tensor φ M 1 m))) := by
  rw [tripleAdj, Adjunction.comp_homEquiv]
  let K : ModuleCat.{max u v s t w} S := ((ModuleCat.induceScalars.{u, v, max u v s t w} φ) ⋙
    (ModuleCat.induceScalars.{v, s, max u v s t w} ψ)).obj M
  let y : K := tensor ψ (Carrier φ M) 1 (tensor φ M 1 m)
  let N' : ModuleCat.{max u v s t w} S := (ModuleCat.restrictScalars.{max u v s t w} χ).obj N
  let q : K ⟶ N' := (ModuleCat.induceRestrictScalarsAdj.{s, t, max u v s t w} χ).homEquiv K N f
  have h₁ : (show N from ((ModuleCat.induceRestrictScalarsAdj.{u, v, max u v s t w} φ).comp
    (ModuleCat.induceRestrictScalarsAdj.{v, s, max u v s t w} ψ)).homEquiv M N' q m) = (show N from q y) := by
    exact composedHomEquiv_apply.{u, v, s, max u v s t w} φ ψ M N' q m
  have h₂ : (show N from q y) = f (tensor χ K 1 y) := by
    exact nativeHomEquiv_apply.{s, t, max u v s t w} χ K N f y
  exact h₁.trans h₂

/-- The composite Hom equivalence detects equality by evaluation on unit tensors. -/
theorem triple_hom_ext (M : ModuleCat.{max u v s t w} k)
    (N : ModuleCat.{max u v s t w} T) {f g : (((ModuleCat.induceScalars.{u, v, max u v s t w} φ) ⋙
      (ModuleCat.induceScalars.{v, s, max u v s t w} ψ)) ⋙ (ModuleCat.induceScalars.{s, t, max u v s t w} χ)).obj M ⟶
      N}
    (h : ∀ m : M,
      f (tensor χ (Carrier ψ (Carrier φ M)) 1
        (tensor ψ (Carrier φ M) 1 (tensor φ M 1 m))) =
      g (tensor χ (Carrier ψ (Carrier φ M)) 1
        (tensor ψ (Carrier φ M) 1 (tensor φ M 1 m)))) : f = g := by
  apply ((tripleAdj.{u, v, s, t, w} φ ψ χ).homEquiv M N).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  have hf : (show N from (tripleAdj.{u, v, s, t, w} φ ψ χ).homEquiv M N f m) =
      f (tensor χ (Carrier ψ (Carrier φ M)) 1
        (tensor ψ (Carrier φ M) 1 (tensor φ M 1 m))) := by
    exact tripleAdj_hom_apply.{u, v, s, t, w} φ ψ χ M N f m
  have hg : (show N from (tripleAdj.{u, v, s, t, w} φ ψ χ).homEquiv M N g m) =
      g (tensor χ (Carrier ψ (Carrier φ M)) 1
        (tensor ψ (Carrier φ M) 1 (tensor φ M 1 m))) := by
    exact tripleAdj_hom_apply.{u, v, s, t, w} φ ψ χ M N g m
  exact hf.trans ((h m).trans hg.symm)

/-- The two induction-composition maps agree after the functor associator. -/
theorem composition_associativity :
    Functor.whiskerRight (compositionIso.{u, v, s, max u v s t w} φ ψ).hom (ModuleCat.induceScalars.{s, t, max u v s t
      w} χ) ≫
        (compositionIso.{u, s, t, max u v s t w} (ψ.comp φ) χ).hom =
      (Functor.associator (ModuleCat.induceScalars.{u, v, max u v s t w} φ) (ModuleCat.induceScalars.{v, s, max u v s
        t w} ψ) (ModuleCat.induceScalars.{s, t, max u v s t w} χ)).hom ≫
        Functor.whiskerLeft (ModuleCat.induceScalars.{u, v, max u v s t w} φ) (compositionIso.{v, s, t, max u v s t w}
          ψ χ).hom ≫
          (compositionIso.{u, v, t, max u v s t w} φ (χ.comp ψ)).hom := by
  apply NatTrans.ext
  funext M
  apply triple_hom_ext.{u, v, s, t, w} φ ψ χ M _
  intro m
  let K : ModuleCat.{max u v s t w} R := (ModuleCat.induceScalars.{u, v, max u v s t w} φ).obj M
  let L : ModuleCat.{max u v s t w} S := (ModuleCat.induceScalars.{v, s, max u v s t w} ψ).obj K
  let L' : ModuleCat.{max u v s t w} S := (ModuleCat.induceScalars.{u, s, max u v s t w} (ψ.comp φ)).obj M
  let N : ModuleCat.{max u v s t w} T := (ModuleCat.induceScalars.{u, t, max u v s t w} (χ.comp (ψ.comp φ))).obj M
  let y : K := tensor φ M 1 m
  let z : L := tensor ψ K 1 y
  let a : (ModuleCat.induceScalars.{s, t, max u v s t w} χ).obj L := tensor χ L 1 z
  let b : L' := tensor (ψ.comp φ) M 1 m
  let μ : L ⟶ L' := (compositionIso.{u, v, s, max u v s t w} φ ψ).hom.app M
  have hμ : μ z = b := compositionIso_hom_unit.{u, v, s, max u v s t w} φ ψ M m
  have hmap : (ModuleCat.induceScalars.{s, t, max u v s t w} χ).map μ a = tensor χ L' 1 (μ z) := by
    exact ModuleCat.induceScalars_map_tensor.{s, t, max u v s t w} χ μ 1 z
  have hmap' : (ModuleCat.induceScalars.{s, t, max u v s t w} χ).map μ a = tensor χ L' 1 b :=
    hmap.trans (congrArg (tensor χ L' 1) hμ)
  have hleft : (compositionIso.{u, s, t, max u v s t w} (ψ.comp φ) χ).hom.app M ((ModuleCat.induceScalars.{s, t, max u
    v s t w} χ).map μ a) =
      (show N from tensor (χ.comp (ψ.comp φ)) M 1 m) :=
    (congrArg ((compositionIso.{u, s, t, max u v s t w} (ψ.comp φ) χ).hom.app M) hmap').trans
      (compositionIso_hom_unit.{u, s, t, max u v s t w} (ψ.comp φ) χ M m)
  have hν : (compositionIso.{v, s, t, max u v s t w} ψ χ).hom.app K a = tensor (χ.comp ψ) K 1 y :=
    compositionIso_hom_unit.{v, s, t, max u v s t w} ψ χ K y
  have hright : (compositionIso.{u, v, t, max u v s t w} φ (χ.comp ψ)).hom.app M ((compositionIso.{v, s, t, max u v s
    t w} ψ χ).hom.app K a) =
      (show N from tensor (χ.comp (ψ.comp φ)) M 1 m) :=
    (congrArg ((compositionIso.{u, v, t, max u v s t w} φ (χ.comp ψ)).hom.app M) hν).trans
      (compositionIso_hom_unit.{u, v, t, max u v s t w} φ (χ.comp ψ) M m)
  exact hleft.trans hright.symm

end Associativity

end ModuleCat.RingHomInduction
