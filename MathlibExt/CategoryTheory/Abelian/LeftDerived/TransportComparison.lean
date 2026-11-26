/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.ExactPostcomposition
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.PrecompositionNaturality
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.BoundaryIsomorphism

/-!
# Left-derived transport of an underlying functor comparison

Let `C,D,E,E′` be abelian, with projective resolutions in `C,D`.
For additive projective- and homology-preserving `U : C → D`, additive
homology-preserving `V : E → E′`, additive `F : C → E`, `G : D → E′`,
and `U ⋙ G ≅ F ⋙ V`, postcomposition and precomposition give
`L_nF ⋙ V ≅ U ⋙ L_nG`. The augmentation, connecting and coefficient
squares follow the same three comparison factors. All four category
object and morphism universes are independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uC vC uD vD uE vE uE' vE'

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasProjectiveResolutions C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasProjectiveResolutions D]
  {E : Type uE} [Category.{vE} E] [Abelian E]
  {E' : Type uE'} [Category.{vE'} E'] [Abelian E']
  (U : C ⥤ D) [U.Additive] [U.PreservesProjectiveObjects] [U.PreservesHomology]
  (V : E ⥤ E') [V.Additive] [V.PreservesHomology]
  (F : C ⥤ E) [F.Additive] (G : D ⥤ E') [G.Additive]
  (e : U ⋙ G ≅ F ⋙ V)

/-- Let `C,D,E,E′` be abelian, with projective resolutions in `C,D`,
`U : C → D` additive and preserving projectives and homology,
`V : E → E′` additive and preserving homology, `F : C → E`,
`G : D → E′` additive, and `e : U ⋙ G ≅ F ⋙ V`. The underlying comparison induces a natural isomorphism
`L_nF ⋙ V ≅ U ⋙ L_nG` in every degree `n`. -/
def leftDerivedTransportIso (n : ℕ) : F.leftDerived n ⋙ V ≅ U ⋙ G.leftDerived n :=
  F.leftDerivedCompIsoOfPreservesHomology V n ≪≫
    NatIso.leftDerived e.symm n ≪≫ leftDerivedPrecompIso U G n

/-- Let `C,D,E,E′` be abelian, with projective resolutions in `C,D`,
`U : C → D` additive and preserving projectives and homology,
`V : E → E′` additive and preserving homology, `F : C → E`,
`G : D → E′` additive, and `e : U ⋙ G ≅ F ⋙ V`. The forward transport is the postcomposition comparison for
`V`, followed by the derived inverse of `e`, and then the
precomposition comparison for `U`. -/
theorem leftDerivedTransportIso_hom (n : ℕ) :
    (leftDerivedTransportIso U V F G e n).hom =
      (F.leftDerivedCompIsoOfPreservesHomology V n).hom ≫
        (NatIso.leftDerived e.symm n).hom ≫ (leftDerivedPrecompIso U G n).hom := rfl

/-- Let `C,D,E,E′` be abelian, with projective resolutions in `C,D`,
`U : C → D` additive and preserving projectives and homology,
`V : E → E′` additive and preserving homology, `F : C → E`,
`G : D → E′` additive, and `e : U ⋙ G ≅ F ⋙ V`. The inverse transport is inverse precomposition for `U`,
followed by the derived map of `e`, and then inverse postcomposition
for `V`. -/
theorem leftDerivedTransportIso_inv (n : ℕ) :
    (leftDerivedTransportIso U V F G e n).inv =
      (leftDerivedPrecompIso U G n).inv ≫
        (NatIso.leftDerived e n).hom ≫ (F.leftDerivedCompIsoOfPreservesHomology V n).inv := by
  simp only [leftDerivedTransportIso, Iso.trans_inv, NatIso.leftDerived_inv,
    Iso.symm_inv, NatIso.leftDerived_hom, Category.assoc]

/-- Let `C,D,E,E′` be abelian, with projective resolutions in `C,D`,
`U : C → D` additive and preserving projectives and homology,
`V : E → E′` additive and preserving homology, `F : C → E`,
`G : D → E′` additive, and `e : U ⋙ G ≅ F ⋙ V`. In degree zero, the forward transport followed by the
augmentation `U ⋙ L₀G → U ⋙ G` equals the augmentation
`L₀F ⋙ V → F ⋙ V` followed by `e⁻¹`. -/
theorem leftDerivedTransportIso_hom_fromLeftDerivedZero :
    (leftDerivedTransportIso U V F G e 0).hom ≫ whiskerLeft U G.fromLeftDerivedZero =
      whiskerRight F.fromLeftDerivedZero V ≫ e.inv := by
  let σ := F.leftDerivedCompIsoOfPreservesHomology V 0
  let θ := NatIso.leftDerived e.symm 0
  let τ := leftDerivedPrecompIso U G 0
  have hτ : τ.hom ≫ whiskerLeft U G.fromLeftDerivedZero =
      (U ⋙ G).fromLeftDerivedZero :=
    leftDerivedPrecompIso_hom_fromLeftDerivedZero U G
  have hθ : θ.hom ≫ (U ⋙ G).fromLeftDerivedZero =
      (F ⋙ V).fromLeftDerivedZero ≫ e.inv :=
    NatTrans.fromLeftDerivedZero_naturality_functor e.inv
  have hσ : σ.hom ≫ (F ⋙ V).fromLeftDerivedZero =
      whiskerRight F.fromLeftDerivedZero V :=
    leftDerivedCompIsoOfPreservesHomology_hom_fromLeftDerivedZero F V
  change (σ.hom ≫ θ.hom ≫ τ.hom) ≫ whiskerLeft U G.fromLeftDerivedZero = _
  calc
    _ = σ.hom ≫ θ.hom ≫ (U ⋙ G).fromLeftDerivedZero := by
      simp only [Category.assoc]
      rw [hτ]
    _ = σ.hom ≫ (F ⋙ V).fromLeftDerivedZero ≫ e.inv := by rw [hθ]
    _ = _ := by rw [← Category.assoc, hσ]

/-- Let `C,D,E,E′` be abelian, with projective resolutions in `C,D`,
`U : C → D` additive and preserving projectives and homology,
`V : E → E′` additive and preserving homology, `F : C → E`,
`G : D → E′` additive, and `e : U ⋙ G ≅ F ⋙ V`. In degree zero, the inverse transport followed by the
augmentation `L₀F ⋙ V → F ⋙ V` equals the augmentation
`U ⋙ L₀G → U ⋙ G` followed by `e`. -/
theorem leftDerivedTransportIso_inv_fromLeftDerivedZero :
    (leftDerivedTransportIso U V F G e 0).inv ≫ whiskerRight F.fromLeftDerivedZero V =
      whiskerLeft U G.fromLeftDerivedZero ≫ e.hom := by
  apply (cancel_epi (leftDerivedTransportIso U V F G e 0).hom).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, leftDerivedTransportIso_hom_fromLeftDerivedZero]
  rw [Category.assoc, e.inv_hom_id, Category.comp_id]

/-- Let `C,D,E,E′` be abelian, with projective resolutions in `C,D`,
`U : C → D` additive and preserving projectives and homology,
`V : E → E′` additive and preserving homology, `F : C → E`,
`G : D → E′` additive, and `e : U ⋙ G ≅ F ⋙ V`. For short exact `S : X₁ → X₂ → X₃`, the forward transport
in degree `n+1` followed by the boundary of `G` on `U(S)` equals
`V` of the boundary of `F` on `S` followed by transport in degree `n`. -/
theorem leftDerivedTransportIso_hom_LDdelta (n : ℕ)
    (S : ShortComplex C) (hS : S.ShortExact) :
    letI : PreservesFiniteLimits U := preservesFiniteLimits_of_preservesHomology U
    letI : PreservesFiniteColimits U := preservesFiniteColimits_of_preservesHomology U
    (leftDerivedTransportIso U V F G e (n + 1)).hom.app S.X₃ ≫
        LeftDerivedDelta.LDdelta G n (S.map U) (hS.map_of_exact U) =
      V.map (LeftDerivedDelta.LDdelta F n S hS) ≫
        (leftDerivedTransportIso U V F G e n).hom.app S.X₁ := by
  let : PreservesFiniteLimits U := preservesFiniteLimits_of_preservesHomology U
  let : PreservesFiniteColimits U := preservesFiniteColimits_of_preservesHomology U
  let σ₃ := F.leftDerivedCompIsoOfPreservesHomology V (n + 1)
  let σ₁ := F.leftDerivedCompIsoOfPreservesHomology V n
  let θ₃ := NatIso.leftDerived e.symm (n + 1)
  let θ₁ := NatIso.leftDerived e.symm n
  let τ₃ := leftDerivedPrecompIso U G (n + 1)
  let τ₁ := leftDerivedPrecompIso U G n
  let d₀ := V.map (LeftDerivedDelta.LDdelta F n S hS)
  let d₁ := LeftDerivedDelta.LDdelta (F ⋙ V) n S hS
  let d₂ := LeftDerivedDelta.LDdelta (U ⋙ G) n S hS
  let d₃ := LeftDerivedDelta.LDdelta G n (S.map U) (hS.map_of_exact U)
  have hσ : σ₃.hom.app S.X₃ ≫ d₁ = d₀ ≫ σ₁.hom.app S.X₁ :=
    leftDerivedCompIsoOfPreservesHomology_hom_LDdelta F V n S hS
  have hθ : θ₃.hom.app S.X₃ ≫ d₂ = d₁ ≫ θ₁.hom.app S.X₁ :=
    NatIso.leftDerived_hom_LDdelta e.symm n S hS
  have hτ : τ₃.hom.app S.X₃ ≫ d₃ = d₂ ≫ τ₁.hom.app S.X₁ :=
    leftDerivedPrecompIso_hom_LDdelta U G n S hS
  change (σ₃.hom.app S.X₃ ≫ θ₃.hom.app S.X₃ ≫ τ₃.hom.app S.X₃) ≫ d₃ =
    d₀ ≫ (σ₁.hom.app S.X₁ ≫ θ₁.hom.app S.X₁ ≫ τ₁.hom.app S.X₁)
  calc
    _ = σ₃.hom.app S.X₃ ≫ θ₃.hom.app S.X₃ ≫
        (d₂ ≫ τ₁.hom.app S.X₁) := by
      simp only [Category.assoc]
      rw [hτ]
    _ = σ₃.hom.app S.X₃ ≫ (d₁ ≫ θ₁.hom.app S.X₁) ≫
        τ₁.hom.app S.X₁ := by
      rw [← Category.assoc (θ₃.hom.app S.X₃), hθ]
    _ = _ := by
      have h := congrArg (fun f => f ≫ θ₁.hom.app S.X₁ ≫ τ₁.hom.app S.X₁) hσ
      simpa only [Category.assoc] using h

/-- Let `C,D,E,E′` be abelian, with projective resolutions in `C,D`,
`U : C → D` additive and preserving projectives and homology,
`V : E → E′` additive and preserving homology, `F : C → E`,
`G : D → E′` additive, and `e : U ⋙ G ≅ F ⋙ V`. For additive `F′,G′`, maps `α : F → F′`, `β : G → G′`,
and `e′ : U ⋙ G′ ≅ F′ ⋙ V` satisfying
`(U ⋙ β) ≫ e′ = e ≫ (α ⋙ V)`, the corresponding derived
transport comparisons commute with `L_nα ⋙ V` and `U ⋙ L_nβ`. -/
theorem leftDerivedTransportIso_naturality
    {F' : C ⥤ E} [F'.Additive] {G' : D ⥤ E'} [G'.Additive]
    (α : F ⟶ F') (β : G ⟶ G') (e' : U ⋙ G' ≅ F' ⋙ V)
    (hBase : whiskerLeft U β ≫ e'.hom = e.hom ≫ whiskerRight α V) (n : ℕ) :
    whiskerRight (NatTrans.leftDerived α n) V ≫
        (leftDerivedTransportIso U V F' G' e' n).hom =
      (leftDerivedTransportIso U V F G e n).hom ≫ whiskerLeft U (NatTrans.leftDerived β n) := by
  let σ := F.leftDerivedCompIsoOfPreservesHomology V n
  let σ' := F'.leftDerivedCompIsoOfPreservesHomology V n
  let θ := NatIso.leftDerived e.symm n
  let θ' := NatIso.leftDerived e'.symm n
  let τ := leftDerivedPrecompIso U G n
  let τ' := leftDerivedPrecompIso U G' n
  have hInv : whiskerRight α V ≫ e'.inv = e.inv ≫ whiskerLeft U β := by
    apply (cancel_mono e'.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hBase]
    simp only [Iso.inv_hom_id_assoc]
  have hθ : NatTrans.leftDerived (whiskerRight α V) n ≫ θ'.hom =
      θ.hom ≫ NatTrans.leftDerived (whiskerLeft U β) n := by
    have h := congrArg (fun γ => NatTrans.leftDerived γ n) hInv
    simpa only [θ, θ', NatIso.leftDerived_hom, Iso.symm_hom,
      NatTrans.leftDerived_comp] using h
  have hσ : whiskerRight (NatTrans.leftDerived α n) V ≫ σ'.hom =
      σ.hom ≫ NatTrans.leftDerived (whiskerRight α V) n :=
    leftDerivedCompIsoOfPreservesHomology_hom_naturality_functor α V n
  have hτ : NatTrans.leftDerived (whiskerLeft U β) n ≫ τ'.hom =
      τ.hom ≫ whiskerLeft U (NatTrans.leftDerived β n) :=
    leftDerivedPrecompIso_hom_naturality_functor U β n
  change whiskerRight (NatTrans.leftDerived α n) V ≫ (σ'.hom ≫ θ'.hom ≫ τ'.hom) =
    (σ.hom ≫ θ.hom ≫ τ.hom) ≫ whiskerLeft U (NatTrans.leftDerived β n)
  calc
    _ = (σ.hom ≫ NatTrans.leftDerived (whiskerRight α V) n) ≫
        θ'.hom ≫ τ'.hom := by rw [← Category.assoc, hσ]
    _ = σ.hom ≫ (θ.hom ≫ NatTrans.leftDerived (whiskerLeft U β) n) ≫
        τ'.hom := by
      have h := congrArg (fun f => σ.hom ≫ f ≫ τ'.hom) hθ
      simpa only [Category.assoc] using h
    _ = _ := by
      have h := congrArg (fun f => σ.hom ≫ θ.hom ≫ f) hτ
      simpa only [Category.assoc] using h

end CategoryTheory.Functor
