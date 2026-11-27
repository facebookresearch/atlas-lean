/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.LogStructures
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Associated log unit condition

The fixed sheaf pushout logification satisfies the log unit condition.

Sources: Kato, *Logarithmic structures of Fontaine--Illusie*, §1;
Nakayama--Ogus, *Relative rounding in toric and logarithmic geometry*,
Definition 3.4 and the following associated-log/chart construction,
https://math.berkeley.edu/~ogus/preprints/nakayamaogus.pdf;
Achinger--Ogus, *Monodromy and log geometry*, §3.1,
https://arxiv.org/abs/1802.02234.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.LogarithmicGeometryWanted

open CategoryTheory CategoryTheory.Limits

universe w

private theorem pushout_elements
    {K M N Q : CommMonCat.{w}} {a : K ⟶ M} {b : K ⟶ N}
    {i : M ⟶ Q} {j : N ⟶ Q} (h : IsPushout a b i j) (q : Q) :
    ∃ m n, i m * j n = q := by
  let S : Submonoid Q :=
    { carrier := {q | ∃ m n, i m * j n = q}
      one_mem' := ⟨1, 1, by simp⟩
      mul_mem' := by
        rintro x y ⟨m, n, rfl⟩ ⟨m', n', rfl⟩
        exact ⟨m * m', n * n', by simp only [map_mul]; ac_rfl⟩ }
  let i' : M ⟶ CommMonCat.of S := CommMonCat.ofHom
    { toFun := fun m => ⟨i m, m, 1, by simp⟩
      map_one' := by apply Subtype.ext; exact map_one i.hom
      map_mul' := fun x y => by apply Subtype.ext; exact map_mul i.hom x y }
  let j' : N ⟶ CommMonCat.of S := CommMonCat.ofHom
    { toFun := fun n => ⟨j n, 1, n, by simp⟩
      map_one' := by apply Subtype.ext; exact map_one j.hom
      map_mul' := fun x y => by apply Subtype.ext; exact map_mul j.hom x y }
  let incl : CommMonCat.of S ⟶ Q := CommMonCat.ofHom S.subtype
  have compat : a ≫ i' = b ≫ j' := by
    ext k
    exact ConcreteCategory.congr_hom h.w k
  let r := h.desc i' j' compat
  have hr : r ≫ incl = 𝟙 Q := by
    apply h.hom_ext
    · simp only [r, ← Category.assoc, IsPushout.inl_desc, Category.comp_id]
      rfl
    · simp only [r, ← Category.assoc, IsPushout.inr_desc, Category.comp_id]
      rfl
  have hq : (r q : Q) = q := ConcreteCategory.congr_hom hr q
  exact hq ▸ (r q).property

private theorem monoid_unit_square
    {K M R Q : CommMonCat.{w}} (a : K ⟶ M)
    (b : K ⟶ CommMonCat.of Rˣ) (α : M ⟶ R)
    (i : M ⟶ Q) (j : CommMonCat.of Rˣ ⟶ Q) (γ : Q ⟶ R)
    (hpre : IsPullback a b α (CommMonCat.ofHom (Units.coeHom R)))
    (hpush : IsPushout a b i j) (hi : i ≫ γ = α)
    (hj : j ≫ γ = CommMonCat.ofHom (Units.coeHom R)) :
    IsPullback j (𝟙 _) γ (CommMonCat.ofHom (Units.coeHom R)) := by
  apply IsPullback.of_map (forget CommMonCat.{w}) (by simpa using hj)
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨?_, ?_, ?_⟩
  · ext u
    exact ConcreteCategory.congr_hom hj u
  · intro x y h
    exact h.2
  · intro q u hu
    obtain ⟨m, v, rfl⟩ := pushout_elements hpush q
    change γ (i m * j v) = (u : R) at hu
    have hm : α m * (v : R) = (u : R) := by
      have hi' : γ (i m) = α m := ConcreteCategory.congr_hom hi m
      have hj' : γ (j v) = (v : R) := ConcreteCategory.congr_hom hj v
      simpa only [map_mul, hi', hj'] using hu
    have hmUnit : IsUnit (α m) :=
      (IsUnit.mul_iff.mp (hm.symm ▸ u.isUnit)).1
    obtain ⟨k, hk, hb⟩ := Types.exists_of_isPullback
      (hpre.map (forget CommMonCat.{w})) m hmUnit.unit hmUnit.unit_spec.symm
    have hmk : i m = j hmUnit.unit := by
      calc
        i m = i (a k) := congrArg i hk.symm
        _ = j (b k) := ConcreteCategory.congr_hom hpush.w k
        _ = j hmUnit.unit := congrArg j hb
    have hv : hmUnit.unit * v = u := by
      apply Units.val_injective
      simpa only [Units.val_mul, hmUnit.unit_spec] using hm
    refine ⟨u, ?_, rfl⟩
    change j u = i m * j v
    rw [hmk, ← map_mul, hv]

open MathlibExt.AlgebraicGeometry.LogStructures

universe u v

private theorem sheaf_unit_square
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (O : RingSheaf J) (P : Prelog J O) {Q : MonoidSheaf J}
    (i : P.left ⟶ Q) (j : units J O ⟶ Q) (γ : Q ⟶ ringMonoids J O)
    (hpush : IsPushout (pullback.fst P.hom (unitInclusion J O))
      (unitRestriction J P) i j)
    (hi : i ≫ γ = P.hom) (hj : j ≫ γ = unitInclusion J O) :
    IsPullback j (𝟙 _) γ (unitInclusion J O) := by
  let K := inverseUnits J P
  let a : K ⟶ P.left := pullback.fst P.hom (unitInclusion J O)
  let b : K ⟶ units J O := unitRestriction J P
  let T := pushout a.hom b.hom
  let i₀ : P.left.obj ⟶ T := pushout.inl a.hom b.hom
  let j₀ : (units J O).obj ⟶ T := pushout.inr a.hom b.hom
  have w : a.hom ≫ P.hom.hom = b.hom ≫ (unitInclusion J O).hom := by
    have w' : a ≫ P.hom = b ≫ unitInclusion J O := pullback.condition
    exact congrArg (fun f : K ⟶ ringMonoids J O => f.hom) w'
  let γ₀ : T ⟶ (ringMonoids J O).obj :=
    pushout.desc P.hom.hom (unitInclusion J O).hom w
  have hp₀ : IsPushout a.hom b.hom i₀ j₀ := IsPushout.of_hasPushout _ _
  have hi₀ : i₀ ≫ γ₀ = P.hom.hom := pushout.inl_desc ..
  have hj₀ : j₀ ≫ γ₀ = (unitInclusion J O).hom := pushout.inr_desc ..
  have hc₀ : IsPullback j₀ (𝟙 _) γ₀ (unitInclusion J O).hom := by
    apply IsPullback.of_forall_isPullback_app
    intro X
    exact monoid_unit_square (a.hom.app X) (b.hom.app X) (P.hom.hom.app X)
      (i₀.app X) (j₀.app X) (γ₀.app X)
      (((IsPullback.of_hasPullback P.hom (unitInclusion J O)).map
        (sheafToPresheaf J CommMonCat)).app X) (hp₀.app X)
      (congrArg (fun f => f.app X) hi₀) (congrArg (fun f => f.app X) hj₀)
  let F := presheafToSheaf J CommMonCat.{max u v}
  let i' : P.left ⟶ F.obj T := (sheafificationIso P.left).hom ≫ F.map i₀
  let j' : units J O ⟶ F.obj T := (sheafificationIso (units J O)).hom ≫ F.map j₀
  let γ' : F.obj T ⟶ ringMonoids J O :=
    F.map γ₀ ≫ (sheafificationIso (ringMonoids J O)).inv
  have hp' : IsPushout a b i' j' := by
    apply (hp₀.map F).of_iso (sheafificationIso K).symm
      (sheafificationIso P.left).symm (sheafificationIso (units J O)).symm (Iso.refl _)
    · exact (sheafificationNatIso J CommMonCat).inv.naturality a
    · exact (sheafificationNatIso J CommMonCat).inv.naturality b
    · simp [i']
    · simp [j']
  have hc' : IsPullback j' (𝟙 _) γ' (unitInclusion J O) := by
    apply (hc₀.map F).of_iso (sheafificationIso (units J O)).symm
      (Iso.refl _) (sheafificationIso (units J O)).symm
      (sheafificationIso (ringMonoids J O)).symm
    · simp [j']
    · simp [F]
    · simp [γ']
    · exact (sheafificationNatIso J CommMonCat).inv.naturality (unitInclusion J O)
  let e := hp'.isoIsPushout _ _ hpush
  have heγ : e.hom ≫ γ = γ' := by
    apply hp'.hom_ext
    · rw [← Category.assoc]
      simp only [e, IsPushout.inl_isoIsPushout_hom, hi]
      dsimp [i', γ']
      simp only [Category.assoc]
      rw [← Category.assoc (F.map i₀), ← F.map_comp, hi₀]
      have hn : F.map P.hom.hom ≫ (sheafificationIso (ringMonoids J O)).inv =
          (sheafificationIso P.left).inv ≫ P.hom :=
        (sheafificationNatIso J CommMonCat).inv.naturality P.hom
      rw [hn]
      simp
    · rw [← Category.assoc]
      simp only [e, IsPushout.inr_isoIsPushout_hom, hj]
      dsimp [j', γ']
      simp only [Category.assoc]
      rw [← Category.assoc (F.map j₀), ← F.map_comp, hj₀]
      have hn : F.map (unitInclusion J O).hom ≫ (sheafificationIso (ringMonoids J O)).inv =
          (sheafificationIso (units J O)).inv ≫ unitInclusion J O :=
        (sheafificationNatIso J CommMonCat).inv.naturality (unitInclusion J O)
      rw [hn]
      simp
  apply hc'.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
  · simp [e]
  · simp
  · simpa using heγ.symm
  · simp

/-- The fixed pushout logification satisfies the genuine unit condition. -/
public theorem associated_log_unit_condition
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (O : RingSheaf J) (P : Prelog J O) :
    isLog J O (associatedPrelog J P)
    := by
  have h := sheaf_unit_square J O P
    (pushout.inl _ _) (pushout.inr _ _) (associatedPrelog J P).hom
    (IsPushout.of_hasPushout _ _) (pushout.inl_desc ..) (pushout.inr_desc ..)
  change IsIso (pullback.snd (associatedPrelog J P).hom (unitInclusion J O))
  let e := h.isoIsPullback _ _
    (IsPullback.of_hasPullback (associatedPrelog J P).hom (unitInclusion J O))
  have he : e.inv = pullback.snd (associatedPrelog J P).hom (unitInclusion J O) := by
    simpa [e] using h.isoIsPullback_inv_snd _ _
      (IsPullback.of_hasPullback (associatedPrelog J P).hom (unitInclusion J O))
  rw [← he]
  infer_instance

end WantedExt.AlgebraicGeometry.LogarithmicGeometryWanted
