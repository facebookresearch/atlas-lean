/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleSectionsClassMap

/-!
# Naturality and uniqueness of positive étale comparisons
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections
variable (X : Scheme.{u})

private theorem original_ext_representative
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ)
    (α : Sheaf.H.{max u w, max u w, u, u + 1} Q (n + 1)) :
    let R := injectiveResolution Q
    ∃ (f : integralSheaf.{u, w} X ⟶ R.cocomplex.X (n + 1))
      (hf : f ≫ R.cocomplex.d (n + 1) (n + 2) = 0),
      R.extMk f (n + 2) rfl hf = α := by
  exact (injectiveResolution Q).extMk_surjective
    (C := Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})
    (X := integralSheaf.{u, w} X)
    (α : Abelian.Ext.{max u w} (integralSheaf.{u, w} X) Q (n + 1)) (n + 2) rfl

/-- The complete positive cycle and representative equations for one comparison family. -/
def positiveExtPacket
    (p : ∀ (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ),
      (positiveShort.{u, w} X Q n).g.hom.ker →+
        Sheaf.H.{max u w, max u w, u, u + 1} Q (n + 1))
    (e : ∀ (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ),
      Sheaf.H.{max u w, max u w, u, u + 1} Q (n + 1) ≃+
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived (n + 1)).obj Q)
    : Prop :=
  ∀ (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ),
    let R := injectiveResolution Q
    Function.Surjective (p Q n) ∧ (positiveShort.{u, w} X Q n).abToCycles.range = (p Q n).ker ∧
    (∀ z, e Q n (p Q n z) = positiveCycleClass.{u, w} X Q n z) ∧
    ∀ (f : integralSheaf.{u, w} X ⟶ R.cocomplex.X (n + 1))
      (hf : f ≫ R.cocomplex.d (n + 1) (n + 2) = 0),
      ∃ z : (positiveShort.{u, w} X Q n).g.hom.ker,
        z.val = integralHomSections.{u, w} X _ f ∧ p Q n z = R.extMk f (n + 2) rfl hf


/-- One internally selected comparison carries every original sheaf map and is unique. -/
theorem positive_ext_original_map_naturality :
    let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}
    ∃ p : ∀ (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ),
      (positiveShort.{u, w} X Q n).g.hom.ker →+ Sheaf.H.{max u w, max u w, u, u + 1} Q (n + 1),
      ∃ e : ∀ (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ),
        Sheaf.H.{max u w, max u w, u, u + 1} Q (n + 1) ≃+ (Γ.rightDerived (n + 1)).obj Q,
      positiveExtPacket.{u, w} X p e ∧
      (∀ (Q Q' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (τ : Q ⟶ Q') (n : ℕ) (α),
        e Q' n (Sheaf.H.map τ (n + 1) α) = (Γ.rightDerived (n + 1)).map τ (e Q n α)) ∧
      ∀ p' e', positiveExtPacket.{u, w} X p' e' → e' = e := by
  intro Γ
  obtain ⟨p, e, h⟩ := positive_ext_cycle_comparison.{u, w} X
  refine ⟨p, e, h, ?_, ?_⟩
  · intro Q Q' τ n α
    let R := injectiveResolution Q
    let R' := injectiveResolution Q'
    let φ : R.Hom R' τ :=
      ⟨InjectiveResolution.desc τ R' R, InjectiveResolution.desc_commutes_zero τ R' R⟩
    obtain ⟨f, hf, hα⟩ := original_ext_representative.{u, w} X Q n α
    obtain ⟨z, hz, hp⟩ := (h Q n).2.2.2 f hf
    obtain ⟨zτ, hval, hclass⟩ := sections_resolution_class_map_naturality.{u, w} X τ n z
    let f' : integralSheaf.{u, w} X ⟶ R'.cocomplex.X (n + 1) :=
      f ≫ φ.hom.f (n + 1)
    have hf' : f' ≫ R'.cocomplex.d (n + 1) (n + 2) = 0 := by
      dsimp only [f']
      rw [Category.assoc, φ.hom.comm, ← Category.assoc, hf, zero_comp]
    obtain ⟨z', hz', hp'⟩ := (h Q' n).2.2.2 f' hf'
    have hzτ : z' = zτ := by
      apply Subtype.ext
      calc
        _ = integralHomSections.{u, w} X _ f' := hz'
        _ = Γ.map (φ.hom.f (n + 1)) (integralHomSections.{u, w} X _ f) :=
          integralHomSections_naturality.{u, w} X f (φ.hom.f (n + 1))
        _ = Γ.map (φ.hom.f (n + 1)) z.val :=
          congrArg (fun x => Γ.map (φ.hom.f (n + 1)) x) hz.symm
        _ = _ := hval.symm
    have hmap : Sheaf.H.map τ (n + 1) (R.extMk f (n + 2) rfl hf) =
        R'.extMk f' (n + 2) rfl hf' := by
      simpa only [Sheaf.H.map_apply] using (R.extMk_comp_mk₀ f (n + 2) rfl hf φ)
    calc
      _ = e Q' n (Sheaf.H.map τ (n + 1) (R.extMk f (n + 2) rfl hf)) :=
        congrArg (fun x => e Q' n (Sheaf.H.map τ (n + 1) x)) hα.symm
      _ = e Q' n (R'.extMk f' (n + 2) rfl hf') := congrArg (e Q' n) hmap
      _ = e Q' n (p Q' n z') := congrArg (e Q' n) hp'.symm
      _ = positiveCycleClass.{u, w} X Q' n z' := (h Q' n).2.2.1 z'
      _ = positiveCycleClass.{u, w} X Q' n zτ :=
        congrArg (positiveCycleClass.{u, w} X Q' n) hzτ
      _ = (Γ.rightDerived (n + 1)).map τ (positiveCycleClass.{u, w} X Q n z) := hclass
      _ = (Γ.rightDerived (n + 1)).map τ (e Q n (p Q n z)) :=
        congrArg (fun x => (Γ.rightDerived (n + 1)).map τ x) ((h Q n).2.2.1 z).symm
      _ = _ := congrArg (fun x => (Γ.rightDerived (n + 1)).map τ (e Q n x)) (hp.trans hα)
  · intro p' e' h'
    funext Q n
    apply DFunLike.coe_injective
    funext α
    let R := injectiveResolution Q
    obtain ⟨f, hf, hα⟩ := original_ext_representative.{u, w} X Q n α
    obtain ⟨z, hz, hp⟩ := (h' Q n).2.2.2 f hf
    obtain ⟨z', hz', hp'⟩ := (h Q n).2.2.2 f hf
    have hcycles : z = z' := Subtype.ext (hz.trans hz'.symm)
    calc
      _ = e' Q n (p' Q n z) := congrArg (e' Q n) (hp.trans hα).symm
      _ = positiveCycleClass.{u, w} X Q n z := (h' Q n).2.2.1 z
      _ = positiveCycleClass.{u, w} X Q n z' :=
        congrArg (positiveCycleClass.{u, w} X Q n) hcycles
      _ = e Q n (p Q n z') := ((h Q n).2.2.1 z').symm
      _ = _ := congrArg (e Q n) (hp'.trans hα)

end AlgebraicGeometry.Scheme.DerivedSections
