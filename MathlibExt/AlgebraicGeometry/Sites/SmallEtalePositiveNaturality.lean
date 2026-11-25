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


section GenericComparisons

universe c v s t

private theorem representativeComparison_naturality
    {C : Type c} [Category.{v} C] [Abelian C]
    [HasInjectiveResolutions C] [HasExt.{t} C]
    (Z : C) (G : C ⥤ AddCommGrpCat.{s}) [G.Additive]
    (V : C → ℕ → Type s) [∀ Q n, AddCommGroup (V Q n)]
    (value : ∀ Q n, V Q n → G.obj ((injectiveResolution Q).cocomplex.X (n + 1)))
    (hvalue : ∀ Q n, Function.Injective (value Q n))
    (eval : ∀ Y : C, (Z ⟶ Y) → G.obj Y)
    (heval : ∀ {Y Y' : C} (f : Z ⟶ Y) (g : Y ⟶ Y'),
      eval Y' (f ≫ g) = G.map g (eval Y f))
    (cl : ∀ Q n, V Q n → (G.rightDerived (n + 1)).obj Q)
    (hcl : ∀ (Q Q' : C) (τ : Q ⟶ Q') (n : ℕ) (z : V Q n),
      ∃ zτ : V Q' n,
        value Q' n zτ = G.map
          ((InjectiveResolution.desc τ (injectiveResolution Q') (injectiveResolution Q)).f
            (n + 1)) (value Q n z) ∧
        cl Q' n zτ = (G.rightDerived (n + 1)).map τ (cl Q n z))
    (p : ∀ Q n, V Q n →+ Abelian.Ext.{t} Z Q (n + 1))
    (e : ∀ Q n, Abelian.Ext.{t} Z Q (n + 1) ≃+ (G.rightDerived (n + 1)).obj Q)
    (hclass : ∀ Q n z, e Q n (p Q n z) = cl Q n z)
    (hrep : ∀ (Q : C) (n : ℕ)
      (f : Z ⟶ (injectiveResolution Q).cocomplex.X (n + 1))
      (hf : f ≫ (injectiveResolution Q).cocomplex.d (n + 1) (n + 2) = 0),
      ∃ z : V Q n,
        value Q n z = eval _ f ∧ p Q n z = (injectiveResolution Q).extMk f (n + 2) rfl hf) :
    ∀ (Q Q' : C) (τ : Q ⟶ Q') (n : ℕ) (α : Abelian.Ext.{t} Z Q (n + 1)),
      e Q' n (α.comp (Abelian.Ext.mk₀ τ) (add_zero (n + 1))) =
        (G.rightDerived (n + 1)).map τ (e Q n α) := by
  intro Q Q' τ n α
  let R : InjectiveResolution Q := injectiveResolution Q
  let R' : InjectiveResolution Q' := injectiveResolution Q'
  let φ : R.Hom R' τ :=
    { hom := InjectiveResolution.desc τ R' R
      ι_f_zero_comp_hom_f_zero := by
        simpa only [CochainComplex.single₀_map_f_zero] using
          InjectiveResolution.desc_commutes_zero τ R' R }
  let a : G.obj (R.cocomplex.X (n + 1)) ⟶ G.obj (R'.cocomplex.X (n + 1)) :=
    G.map (φ.hom.f (n + 1))
  let d : (G.rightDerived (n + 1)).obj Q ⟶ (G.rightDerived (n + 1)).obj Q' :=
    (G.rightDerived (n + 1)).map τ
  obtain ⟨f, hf, hα⟩ := R.extMk_surjective α (n + 2) rfl
  obtain ⟨z, hz, hp⟩ := hrep Q n f hf
  obtain ⟨zτ, hval, hmapClass⟩ := hcl Q Q' τ n z
  let f' : Z ⟶ R'.cocomplex.X (n + 1) := f ≫ φ.hom.f (n + 1)
  have hf' : f' ≫ R'.cocomplex.d (n + 1) (n + 2) = 0 := by
    dsimp only [f']
    rw [Category.assoc, φ.hom.comm, ← Category.assoc, hf, zero_comp]
  obtain ⟨z', hz', hp'⟩ := hrep Q' n f' hf'
  have hzτ : z' = zτ := by
    apply hvalue Q' n
    calc
      _ = eval _ f' := hz'
      _ = a (eval _ f) := heval f (φ.hom.f (n + 1))
      _ = a (value Q n z) := congrArg a hz.symm
      _ = _ := hval.symm
  have hmap :
      (R.extMk f (n + 2) rfl hf).comp (Abelian.Ext.mk₀ τ) (add_zero (n + 1)) =
        R'.extMk f' (n + 2) rfl hf' :=
    R.extMk_comp_mk₀ f (n + 2) rfl hf φ
  change e Q' n (α.comp (Abelian.Ext.mk₀ τ) (add_zero (n + 1))) = d (e Q n α)
  calc
    _ = e Q' n ((R.extMk f (n + 2) rfl hf).comp
        (Abelian.Ext.mk₀ τ) (add_zero (n + 1))) :=
      congrArg (fun x => e Q' n (x.comp (Abelian.Ext.mk₀ τ) (add_zero (n + 1)))) hα.symm
    _ = e Q' n (R'.extMk f' (n + 2) rfl hf') := congrArg (e Q' n) hmap
    _ = e Q' n (p Q' n z') := congrArg (e Q' n) hp'.symm
    _ = cl Q' n z' := hclass Q' n z'
    _ = cl Q' n zτ := congrArg (cl Q' n) hzτ
    _ = d (cl Q n z) := hmapClass
    _ = d (e Q n (p Q n z)) := congrArg d (hclass Q n z).symm
    _ = _ := congrArg (fun x => d (e Q n x)) (hp.trans hα)

private theorem representativeComparison_unique
    {C : Type c} [Category.{v} C] [Abelian C]
    [HasInjectiveResolutions C] [HasExt.{t} C]
    (Z : C) (G : C ⥤ AddCommGrpCat.{s}) [G.Additive]
    (V : C → ℕ → Type s) [∀ Q n, AddCommGroup (V Q n)]
    (value : ∀ Q n, V Q n → G.obj ((injectiveResolution Q).cocomplex.X (n + 1)))
    (hvalue : ∀ Q n, Function.Injective (value Q n))
    (eval : ∀ Y : C, (Z ⟶ Y) → G.obj Y)
    (cl : ∀ Q n, V Q n → (G.rightDerived (n + 1)).obj Q)
    (p p' : ∀ Q n, V Q n →+ Abelian.Ext.{t} Z Q (n + 1))
    (e e' : ∀ Q n, Abelian.Ext.{t} Z Q (n + 1) ≃+ (G.rightDerived (n + 1)).obj Q)
    (hclass : ∀ Q n z, e Q n (p Q n z) = cl Q n z)
    (hrep : ∀ (Q : C) (n : ℕ)
      (f : Z ⟶ (injectiveResolution Q).cocomplex.X (n + 1))
      (hf : f ≫ (injectiveResolution Q).cocomplex.d (n + 1) (n + 2) = 0),
      ∃ z : V Q n,
        value Q n z = eval _ f ∧ p Q n z = (injectiveResolution Q).extMk f (n + 2) rfl hf)
    (hclass' : ∀ Q n z, e' Q n (p' Q n z) = cl Q n z)
    (hrep' : ∀ (Q : C) (n : ℕ)
      (f : Z ⟶ (injectiveResolution Q).cocomplex.X (n + 1))
      (hf : f ≫ (injectiveResolution Q).cocomplex.d (n + 1) (n + 2) = 0),
      ∃ z : V Q n,
        value Q n z = eval _ f ∧ p' Q n z = (injectiveResolution Q).extMk f (n + 2) rfl hf) :
    e' = e := by
  funext Q n
  apply DFunLike.coe_injective
  funext α
  let R : InjectiveResolution Q := injectiveResolution Q
  obtain ⟨f, hf, hα⟩ := R.extMk_surjective α (n + 2) rfl
  obtain ⟨z, hz, hp⟩ := hrep' Q n f hf
  obtain ⟨z', hz', hp'⟩ := hrep Q n f hf
  have hcycles : z = z' := hvalue Q n (hz.trans hz'.symm)
  calc
    _ = e' Q n (p' Q n z) := congrArg (e' Q n) (hp.trans hα).symm
    _ = cl Q n z := hclass' Q n z
    _ = cl Q n z' := congrArg (cl Q n) hcycles
    _ = e Q n (p Q n z') := (hclass Q n z').symm
    _ = _ := congrArg (e Q n) (hp'.trans hα)

end GenericComparisons

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
  obtain ⟨p, e, hPacket⟩ := positive_ext_cycle_comparison.{u, w} X
  let C := Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}
  let : HasExt.{max u w} C := smallEtaleHasExt.{u, w} X
  let G : C ⥤ AddCommGrpCat.{max u w} := Γ
  let Z : C := integralSheaf.{u, w} X
  let V : C → ℕ → Type (max u w) := fun Q n => (positiveShort.{u, w} X Q n).g.hom.ker
  let value : ∀ Q n, V Q n → G.obj ((injectiveResolution Q).cocomplex.X (n + 1)) :=
    fun _ _ z => z.val
  have hvalue : ∀ Q n, Function.Injective (value Q n) :=
    fun _ _ _ _ h => Subtype.ext h
  let eval : ∀ Y : C, (Z ⟶ Y) → G.obj Y :=
    fun Y f => integralHomSections.{u, w} X Y f
  let cl : ∀ Q n, V Q n → (G.rightDerived (n + 1)).obj Q :=
    positiveCycleClass.{u, w} X
  have heval : ∀ {Y Y' : C} (f : Z ⟶ Y) (g : Y ⟶ Y'),
      eval Y' (f ≫ g) = G.map g (eval Y f) :=
    fun f g => integralHomSections_naturality.{u, w} X f g
  have hcl : ∀ (Q Q' : C) (τ : Q ⟶ Q') (n : ℕ) (z : V Q n),
      ∃ zτ : V Q' n,
        value Q' n zτ = G.map
          ((InjectiveResolution.desc τ (injectiveResolution Q') (injectiveResolution Q)).f
            (n + 1)) (value Q n z) ∧
        cl Q' n zτ = (G.rightDerived (n + 1)).map τ (cl Q n z) :=
    fun _ _ τ n z => sections_resolution_class_map_naturality.{u, w} X τ n z
  have hclass : ∀ Q n z, e Q n (p Q n z) = cl Q n z :=
    fun Q n z => (hPacket Q n).2.2.1 z
  have hrep : ∀ (Q : C) (n : ℕ)
      (f : Z ⟶ (injectiveResolution Q).cocomplex.X (n + 1))
      (hf : f ≫ (injectiveResolution Q).cocomplex.d (n + 1) (n + 2) = 0),
      ∃ z : V Q n,
        value Q n z = eval _ f ∧ p Q n z = (injectiveResolution Q).extMk f (n + 2) rfl hf :=
    fun Q n f hf => (hPacket Q n).2.2.2 f hf
  have hNatural := representativeComparison_naturality
    Z G V value hvalue eval heval cl hcl p e hclass hrep
  refine ⟨p, e, hPacket, ?_, ?_⟩
  · intro Q Q' τ n α
    simpa only [Sheaf.H.map_apply] using hNatural Q Q' τ n α
  · intro p' e' h'
    exact representativeComparison_unique Z G V value hvalue eval cl p p' e e'
      hclass hrep (fun Q n z => (h' Q n).2.2.1 z)
      (fun Q n f hf => (h' Q n).2.2.2 f hf)

end AlgebraicGeometry.Scheme.DerivedSections
