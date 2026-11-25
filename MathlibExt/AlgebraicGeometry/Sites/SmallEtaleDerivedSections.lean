/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtalePositiveNaturality

/-!
# Derived sections of small étale sheaves
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w v v'
namespace AlgebraicGeometry.Scheme.DerivedSections
variable (X : Scheme.{u})
private def joinDegree {H : ℕ → Type v} {D : ℕ → Type v'}
    [∀ q, Add (H q)] [∀ q, Add (D q)]
    (e0 : H 0 ≃+ D 0) (ep : ∀ n, H (n + 1) ≃+ D (n + 1)) (q : ℕ) : H q ≃+ D q :=
  match q with
  | 0 => e0
  | n + 1 => ep n

private def zeroDerivedEquiv
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    Sheaf.H.{max u w, max u w, u, u + 1} Q 0 ≃+
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived 0).obj Q :=
  (Sheaf.H.equiv₀ Q (identityEtaleIsTerminal X)).trans
    (((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
      (identityEtaleIsTerminal X)).app Q).addCommGroupIsoToAddEquiv.symm.trans
        (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf.app
          Q).addCommGroupIsoToAddEquiv.symm))

private theorem zeroDerivedEquiv_sections
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})
    (x : Sheaf.H.{max u w, max u w, u, u + 1} Q 0) :
    (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
      (identityEtaleIsTerminal X)).hom.app Q
      (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf.hom.app
        Q) (zeroDerivedEquiv.{u, w} X Q x)) =
      Sheaf.H.equiv₀ Q (identityEtaleIsTerminal X) x := by
  let a0 := (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
    (identityEtaleIsTerminal X)).app Q |>.addCommGroupIsoToAddEquiv
  let r0 := (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf.app
    Q |>.addCommGroupIsoToAddEquiv
  change a0 (r0 (r0.symm (a0.symm (Sheaf.H.equiv₀ Q (identityEtaleIsTerminal X) x)))) = _
  rw [r0.apply_symm_apply, a0.apply_symm_apply]

private theorem zeroDerivedEquiv_naturality
    {Q Q' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}} (f : Q ⟶ Q')
    (x : Sheaf.H.{max u w, max u w, u, u + 1} Q 0) :
    zeroDerivedEquiv.{u, w} X Q' (Sheaf.H.map f 0 x) =
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived 0).map f
        (zeroDerivedEquiv.{u, w} X Q x) := by
  let D := (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf
  let S := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
    (identityEtaleIsTerminal X)
  apply (D.app Q').addCommGroupIsoToAddEquiv.injective
  apply (S.app Q').addCommGroupIsoToAddEquiv.injective
  change S.hom.app Q' (D.hom.app Q' (zeroDerivedEquiv.{u, w} X Q' (Sheaf.H.map f 0 x))) =
    S.hom.app Q' (D.hom.app Q'
      (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived 0).map f
        (zeroDerivedEquiv.{u, w} X Q x)))
  rw [zeroDerivedEquiv_sections.{u, w} X Q']
  have hd := ConcreteCategory.congr_hom (D.hom.naturality f)
    (zeroDerivedEquiv.{u, w} X Q x)
  have hs := ConcreteCategory.congr_hom (S.hom.naturality f)
    (D.hom.app Q (zeroDerivedEquiv.{u, w} X Q x))
  simp only [ConcreteCategory.comp_apply] at hd hs
  calc
    _ = f.hom.app (op (Scheme.Etale.mk (𝟙 X)))
        (Sheaf.H.equiv₀ Q (identityEtaleIsTerminal X) x) :=
      (Sheaf.H.equiv₀_naturality (identityEtaleIsTerminal X) f x).symm
    _ = f.hom.app (op (Scheme.Etale.mk (𝟙 X)))
        (S.hom.app Q (D.hom.app Q (zeroDerivedEquiv.{u, w} X Q x))) :=
      congrArg (f.hom.app (op (Scheme.Etale.mk (𝟙 X))))
        (zeroDerivedEquiv_sections.{u, w} X Q x).symm
    _ = S.hom.app Q' ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).map f
        (D.hom.app Q (zeroDerivedEquiv.{u, w} X Q x))) := hs.symm
    _ = _ := congrArg (S.hom.app Q') hd.symm


/-- Actual Ext cohomology is naturally the right-derived global sections of every original sheaf. -/
theorem original_small_etale_derived_sections :
    let J := X.smallEtaleTopology
    let Γ := Sheaf.Γ J AddCommGrpCat.{max u w}
    let L := liftCoefficients.{u, w} X
    ∃ e : ∀ (F : Sheaf J AddCommGrpCat.{w}) (q : ℕ),
        Sheaf.H.{max u w, max u w, u, u + 1} (L.obj F) q ≃+
          (Γ.rightDerived q).obj (L.obj F),
      (∀ (F F' : Sheaf J AddCommGrpCat.{w}) (f : F ⟶ F') (q : ℕ)
        (x : Sheaf.H.{max u w, max u w, u, u + 1} (L.obj F) q),
        e F' q (Sheaf.H.map (L.map f) q x) =
          (Γ.rightDerived q).map (L.map f) (e F q x)) ∧
      (∀ (F : Sheaf J AddCommGrpCat.{w})
        (x : Sheaf.H.{max u w, max u w, u, u + 1} (L.obj F) 0),
        (Sheaf.ΓNatIsoSheafSections J AddCommGrpCat.{max u w}
          (identityEtaleIsTerminal X)).hom.app (L.obj F)
          ((Γ.rightDerivedZeroIsoSelf.hom.app (L.obj F)) (e F 0 x)) =
          Sheaf.H.equiv₀ (L.obj F) (identityEtaleIsTerminal X) x) ∧
      (∀ (F : Sheaf J AddCommGrpCat.{w}) (U V : X.Etaleᵒᵖ) (θ : U ⟶ V)
        (x : F.obj.obj U),
        (L.obj F).obj.map θ (ULift.up x) = ULift.up (F.obj.map θ x)) ∧
      (∀ (F F' : Sheaf J AddCommGrpCat.{w}) (f : F ⟶ F') (U : X.Etaleᵒᵖ)
        (x : F.obj.obj U),
        (L.map f).hom.app U (ULift.up x) = ULift.up (f.hom.app U x)) ∧
      ∃ p ep, positiveExtPacket.{u, w} X p ep ∧
        ∀ (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ),
          e F (n + 1) = ep (L.obj F) n := by
  intro J Γ L
  obtain ⟨p, ep, hPacket, hn, hU⟩ := positive_ext_original_map_naturality.{u, w} X
  refine ⟨fun F q => joinDegree
    (H := fun j => Sheaf.H.{max u w, max u w, u, u + 1} (L.obj F) j)
    (D := fun j => (Γ.rightDerived j).obj (L.obj F))
    (zeroDerivedEquiv.{u, w} X (L.obj F)) (fun n => ep (L.obj F) n) q, ?_, ?_, ?_, ?_, ?_⟩
  · intro F F' f q x
    cases q with
    | zero => exact zeroDerivedEquiv_naturality.{u, w} X (L.map f) x
    | succ n => exact hn (L.obj F) (L.obj F') (L.map f) n x
  · intro F x
    exact zeroDerivedEquiv_sections.{u, w} X (L.obj F) x
  · intros
    rfl
  · intros
    rfl
  · exact ⟨p, ep, hPacket, fun _ _ => rfl⟩

end AlgebraicGeometry.Scheme.DerivedSections
