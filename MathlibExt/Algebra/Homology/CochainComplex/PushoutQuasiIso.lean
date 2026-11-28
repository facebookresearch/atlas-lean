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

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import MathlibExt.Algebra.Homology.HomotopyCategory.MappingConeQuasiIso

/-!
# Gluing quasi-isomorphisms along cochain pushouts

Let V be an abelian category and consider arbitrary integer-indexed cochain
complexes in V. A pushout square with maps i:A → B, f:A → Z and legs
inB:B → P, inZ:Z → P gives the short complex
A —(i,−f)→ B ⊞ Z —[inB,inZ]→ P.
The second map is the cokernel of the first. If i is monic, this sequence
is short exact.

For a commuting map between two such pushout squares with monic
distinguished maps i and i′, quasi-isomorphisms on A, B and Z imply a
quasi-isomorphism on the apices P. The map of short complexes has components
x, y ⊞ z and p, preserving the signed first map and both pushout legs.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {V : Type u} [Category.{v} V] [Abelian V]
variable {A B Z P A' B' Z' P' : CochainComplex V ℤ}
variable {i : A ⟶ B} {f : A ⟶ Z} {inB : B ⟶ P} {inZ : Z ⟶ P}
variable {i' : A' ⟶ B'} {f' : A' ⟶ Z'} {inB' : B' ⟶ P'} {inZ' : Z' ⟶ P'}

/-- Let V be abelian and let a pushout square of integer-indexed cochain
complexes have maps i:A → B, f:A → Z and legs inB:B → P, inZ:Z → P.
The associated short complex is
A —(i,−f)→ B ⊞ Z —[inB,inZ]→ P.
The composite is zero by the commuting-square identity. -/
@[simps! X₁ X₂ X₃ f g]
def pushoutShortComplex (hP : IsPushout i f inB inZ) :
    ShortComplex (CochainComplex V ℤ) :=
  ShortComplex.mk (biprod.lift i (-f)) (biprod.desc inB inZ) (by
    rw [biprod.lift_desc, Preadditive.neg_comp, hP.w, add_neg_cancel])

/-- For a pushout square of integer-indexed cochain complexes in an abelian
category V, with maps i:A → B, f:A → Z and legs inB:B → P, inZ:Z → P,
the map [inB,inZ]:B ⊞ Z → P is the cokernel of
(i,−f):A → B ⊞ Z. The corresponding cokernel cofork is a colimit. -/
def pushoutShortComplexIsColimit (hP : IsPushout i f inB inZ) :
    IsColimit (CokernelCofork.ofπ (pushoutShortComplex hP).g (pushoutShortComplex hP).zero) := by
  let S := pushoutShortComplex hP
  have hπ : (CokernelCofork.ofπ S.g S.zero).π = biprod.desc inB inZ := rfl
  refine Cofork.IsColimit.mk _ ?_ ?_ ?_
  · intro c
    refine hP.desc (biprod.inl ≫ c.π) (biprod.inr ≫ c.π) ?_
    have h : biprod.lift i (-f) ≫ c.π = 0 := CokernelCofork.condition c
    have he : biprod.lift i (-f) ≫ c.π =
        i ≫ (biprod.inl ≫ c.π) - f ≫ (biprod.inr ≫ c.π) := by
      calc
        _ = (i ≫ biprod.inl + (-f) ≫ biprod.inr) ≫ c.π :=
          congrArg (fun t => t ≫ c.π) biprod.lift_eq
        _ = (i ≫ biprod.inl) ≫ c.π + ((-f) ≫ biprod.inr) ≫ c.π :=
          Preadditive.add_comp _ _ _ _ _ _
        _ = i ≫ (biprod.inl ≫ c.π) + (-f) ≫ (biprod.inr ≫ c.π) :=
          congrArg₂ (fun a b => a + b)
            (Category.assoc i biprod.inl c.π) (Category.assoc (-f) biprod.inr c.π)
        _ = _ := by
          simpa only [sub_eq_add_neg] using
            congrArg (fun a => i ≫ (biprod.inl ≫ c.π) + a)
              (Preadditive.neg_comp f (biprod.inr ≫ c.π))
    exact sub_eq_zero.mp (he.symm.trans h)
  · intro c
    change (biprod.desc inB inZ) ≫ _ = c.π
    apply biprod.hom_ext'
    · rw [← Category.assoc, biprod.inl_desc, IsPushout.inl_desc]
    · rw [← Category.assoc, biprod.inr_desc, IsPushout.inr_desc]
  · intro c m hm
    rw [hπ] at hm
    apply hP.hom_ext
    · simp only [IsPushout.inl_desc]
      have h₁ := congrArg (fun t => (biprod.inl : B ⟶ B ⊞ Z) ≫ t) hm
      exact (congrArg (fun t => t ≫ m) (biprod.inl_desc inB inZ)).symm.trans
        ((Category.assoc biprod.inl (biprod.desc inB inZ) m).trans h₁)
    · simp only [IsPushout.inr_desc]
      have h₂ := congrArg (fun t => (biprod.inr : Z ⟶ B ⊞ Z) ≫ t) hm
      exact (congrArg (fun t => t ≫ m) (biprod.inr_desc inB inZ)).symm.trans
        ((Category.assoc biprod.inr (biprod.desc inB inZ) m).trans h₂)

/-- For a pushout square of integer-indexed cochain complexes in an abelian
category V, if its distinguished map i:A → B is monic, the signed
biproduct sequence
0 → A —(i,−f)→ B ⊞ Z —[inB,inZ]→ P → 0
is short exact. -/
theorem pushoutShortComplex_shortExact (hP : IsPushout i f inB inZ) [Mono i] :
    (pushoutShortComplex hP).ShortExact := by
  let S := pushoutShortComplex hP
  have hc : IsColimit (CokernelCofork.ofπ S.g S.zero) := pushoutShortComplexIsColimit hP
  have hmono : Mono S.f := by
    change Mono (biprod.lift i (-f))
    have hfac : (biprod.lift i (-f)) ≫ (biprod.fst : B ⊞ Z ⟶ B) = i := by simp
    exact mono_of_mono_fac hfac
  exact ShortComplex.ShortExact.mk' (S.exact_of_g_is_cokernel hc) hmono
    (epi_of_isColimit_cofork hc)

private theorem quasiIso_biprod_map {K L K' L' : CochainComplex V ℤ}
    (y : K ⟶ K') (z : L ⟶ L') (hy : QuasiIso y) (hz : QuasiIso z) :
    QuasiIso (biprod.map y z) := by
  let _ : QuasiIso y := hy
  let _ : QuasiIso z := hz
  rw [quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H : CochainComplex V ℤ ⥤ V := HomologicalComplex.homologyFunctor V (.up ℤ) j
  let _ : PreservesBinaryBiproducts H := preservesBinaryBiproducts_of_preservesBiproducts H
  let e₁ : H.obj (K ⊞ L) ≅ H.obj K ⊞ H.obj L := H.mapBiprod K L
  let e₂ : H.obj (K' ⊞ L') ≅ H.obj K' ⊞ H.obj L' := H.mapBiprod K' L'
  let _ : IsIso (H.map y) := by change IsIso (HomologicalComplex.homologyMap y j); infer_instance
  let _ : IsIso (H.map z) := by change IsIso (HomologicalComplex.homologyMap z j); infer_instance
  let _ : IsIso (biprod.map (H.map y) (H.map z)) := by
    change IsIso (biprod.mapIso (asIso (H.map y)) (asIso (H.map z))).hom
    infer_instance
  have h₁fst : e₁.hom ≫ biprod.fst = H.map (biprod.fst : K ⊞ L ⟶ K) := by
    change biprod.lift (H.map biprod.fst) (H.map biprod.snd) ≫ biprod.fst = _
    exact biprod.lift_fst _ _
  have h₁snd : e₁.hom ≫ biprod.snd = H.map (biprod.snd : K ⊞ L ⟶ L) := by
    change biprod.lift (H.map biprod.fst) (H.map biprod.snd) ≫ biprod.snd = _
    exact biprod.lift_snd _ _
  have h₂fst : e₂.hom ≫ biprod.fst = H.map (biprod.fst : K' ⊞ L' ⟶ K') := by
    change biprod.lift (H.map biprod.fst) (H.map biprod.snd) ≫ biprod.fst = _
    exact biprod.lift_fst _ _
  have h₂snd : e₂.hom ≫ biprod.snd = H.map (biprod.snd : K' ⊞ L' ⟶ L') := by
    change biprod.lift (H.map biprod.fst) (H.map biprod.snd) ≫ biprod.snd = _
    exact biprod.lift_snd _ _
  have hmap : H.map (biprod.map y z) ≫ e₂.hom = e₁.hom ≫ biprod.map (H.map y) (H.map z) := by
    apply biprod.hom_ext
    · calc
        _ = H.map (biprod.map y z) ≫ H.map (biprod.fst : K' ⊞ L' ⟶ K') := by
          rw [Category.assoc, h₂fst]
        _ = H.map (biprod.map y z ≫ biprod.fst) := (H.map_comp _ _).symm
        _ = H.map (biprod.fst ≫ y) := congrArg H.map (biprod.map_fst y z)
        _ = H.map biprod.fst ≫ H.map y := H.map_comp _ _
        _ = (e₁.hom ≫ biprod.fst) ≫ H.map y :=
          congrArg (fun t => t ≫ H.map y) h₁fst.symm
        _ = _ := by simp only [Category.assoc, biprod.map_fst]
    · calc
        _ = H.map (biprod.map y z) ≫ H.map (biprod.snd : K' ⊞ L' ⟶ L') := by
          rw [Category.assoc, h₂snd]
        _ = H.map (biprod.map y z ≫ biprod.snd) := (H.map_comp _ _).symm
        _ = H.map (biprod.snd ≫ z) := congrArg H.map (biprod.map_snd y z)
        _ = H.map biprod.snd ≫ H.map z := H.map_comp _ _
        _ = (e₁.hom ≫ biprod.snd) ≫ H.map z :=
          congrArg (fun t => t ≫ H.map z) h₁snd.symm
        _ = _ := by simp only [Category.assoc, biprod.map_snd]
  have heq : H.map (biprod.map y z) =
      e₁.hom ≫ biprod.map (H.map y) (H.map z) ≫ e₂.inv := by
    calc
      _ = (H.map (biprod.map y z) ≫ e₂.hom) ≫ e₂.inv := by simp
      _ = (e₁.hom ≫ biprod.map (H.map y) (H.map z)) ≫ e₂.inv :=
        congrArg (fun t => t ≫ e₂.inv) hmap
      _ = _ := Category.assoc _ _ _
  change IsIso (H.map (biprod.map y z))
  rw [heq]
  infer_instance

/-- Let V be abelian, and consider two pushout squares of integer-indexed
cochain complexes with maps i,f,inB,inZ and i′,f′,inB′,inZ′.
Suppose x:A → A′, y:B → B′, z:Z → Z′ and p:P → P′ satisfy
y ∘ i=i′ ∘ x, z ∘ f=f′ ∘ x,
p ∘ inB=inB′ ∘ y and p ∘ inZ=inZ′ ∘ z.
They induce a map of the signed pushout short complexes with three
components x, y ⊞ z and p. -/
@[simps! τ₁ τ₂ τ₃]
def pushoutShortComplexMap (hP : IsPushout i f inB inZ) (hP' : IsPushout i' f' inB' inZ')
    (x : A ⟶ A') (y : B ⟶ B') (z : Z ⟶ Z') (p : P ⟶ P')
    (wi : i ≫ y = x ≫ i') (wf : f ≫ z = x ≫ f')
    (wB : inB ≫ p = y ≫ inB') (wZ : inZ ≫ p = z ≫ inZ') :
    pushoutShortComplex hP ⟶ pushoutShortComplex hP' where
  τ₁ := x
  τ₂ := biprod.map y z
  τ₃ := p
  comm₁₂ := by
    apply biprod.hom_ext
    · simpa only [pushoutShortComplex, Category.assoc, biprod.lift_fst,
        biprod.lift_fst_assoc, biprod.map_fst] using wi.symm
    · simpa only [pushoutShortComplex, Category.assoc, biprod.lift_snd,
        biprod.lift_snd_assoc, biprod.map_snd, Preadditive.comp_neg, Preadditive.neg_comp] using
        congrArg (fun t => -t) wf.symm
  comm₂₃ := by
    apply biprod.hom_ext'
    · simpa only [pushoutShortComplex, Category.assoc, biprod.inl_map_assoc,
        biprod.inl_desc, biprod.inl_desc_assoc] using wB.symm
    · simpa only [pushoutShortComplex, Category.assoc, biprod.inr_map_assoc,
        biprod.inr_desc, biprod.inr_desc_assoc] using wZ.symm

/-- Let V be an abelian category. For a commuting map between two pushout
squares of integer-indexed cochain complexes, with monic distinguished
maps i:A → B and i′:A′ → B′, let the four vertex maps be
x:A → A′, y:B → B′, z:Z → Z′ and p:P → P′, commuting with the two
span maps and the two pushout legs. If x, y and z are quasi-isomorphisms,
then p is a quasi-isomorphism. -/
theorem quasiIso_of_pushout (hP : IsPushout i f inB inZ) (hP' : IsPushout i' f' inB' inZ')
    [Mono i] [Mono i'] (x : A ⟶ A') (y : B ⟶ B') (z : Z ⟶ Z') (p : P ⟶ P')
    (wi : i ≫ y = x ≫ i') (wf : f ≫ z = x ≫ f')
    (wB : inB ≫ p = y ≫ inB') (wZ : inZ ≫ p = z ≫ inZ')
    (hx : QuasiIso x) (hy : QuasiIso y) (hz : QuasiIso z) : QuasiIso p := by
  let S := pushoutShortComplex hP
  let S' := pushoutShortComplex hP'
  let t : S ⟶ S' := pushoutShortComplexMap hP hP' x y z p wi wf wB wZ
  have hS : S.ShortExact := pushoutShortComplex_shortExact hP
  have hS' : S'.ShortExact := pushoutShortComplex_shortExact hP'
  let δ := mappingCone.descShortComplex S
  let δ' := mappingCone.descShortComplex S'
  let u := mappingCone.map S.f S'.f x (biprod.map y z) t.comm₁₂.symm
  have hu : QuasiIso u := mappingCone.quasiIso_map S.f S'.f x (biprod.map y z)
    t.comm₁₂.symm hx (quasiIso_biprod_map y z hy hz)
  let _ : QuasiIso δ := mappingCone.quasiIso_descShortComplex hS
  let _ : QuasiIso δ' := mappingCone.quasiIso_descShortComplex hS'
  have hcomm : u ≫ δ' = δ ≫ p := mappingCone.map_descShortComplex S S' t
  let _ : QuasiIso (δ ≫ p) := by
    rw [← hcomm]
    exact _root_.quasiIso_comp u δ' (hφ := hu) (hφ' := inferInstance)
  exact _root_.quasiIso_of_comp_left δ p

end CochainComplex

end
