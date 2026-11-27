/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed proof port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/DoldKan/Monoidal.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only module/namespace paths are adapted for Atlas.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import Mathlib.AlgebraicTopology.DoldKan.EquivalencePseudoabelian
public import MathlibExt.CategoryTheory.DGSourceMore.AlexanderWhitney
public import MathlibExt.CategoryTheory.DGSourceMore.MonoidalFunctor

/-!
# The monoidal structure of the Dold–Kan correspondence

Let `C` be a preadditive monoidal category whose tensor product is additive in each variable
(`CategoryTheory.MonoidalPreadditive C`), with finite coproducts and idempotent complete, for
instance the category of modules over a commutative ring.  Mathlib's Dold–Kan equivalence
`CategoryTheory.Idempotents.DoldKan.equivalence : SimplicialObject C ≌ ChainComplex C ℕ` has
functor the normalized chains `N` and inverse `Γ`.  This file makes `N` oplax monoidal through
the Alexander–Whitney map, and hence `Γ` lax monoidal as its right adjoint.  The lax structure
of `Γ` is what composes the simplicial mapping objects `Γ(τ_{≥0} Hom(x, y))` of the simplicial
enrichment of a differential graded category (J. Lurie, *Higher Algebra*, Construction 1.3.1.13).

The normalized chains `N X` are the direct summand of the alternating face map complex of `X`
cut out by the idempotent `PInfty`, whose kernel is spanned by the degenerate simplices, with
inclusion `CategoryTheory.Idempotents.DoldKan.inclusionN` and projection
`CategoryTheory.Idempotents.DoldKan.PInftyToN`, bundled as the retract
`CategoryTheory.Idempotents.DoldKan.retractN`.  For an abelian category `C` this summand is
isomorphic to the normalized Moore complex
(`AlgebraicTopology.DoldKan.N₁_iso_normalizedMooreComplex_comp_toKaroubi`).  The key point is
that the Alexander–Whitney map of `CategoryTheory.SimplicialObject.alexanderWhitney` preserves
degenerate chains
(`CategoryTheory.SimplicialObject.QInfty_comp_alexanderWhitney_comp_tensorHom_PInfty`): every
summand of the Alexander–Whitney map of a degenerate simplex has a degenerate front or back face.
The comultiplication of the alternating face map complex therefore passes to the retract `N`
(`CategoryTheory.Functor.OplaxMonoidal.ofRetract`).

## Main definitions and results

* `CategoryTheory.SimplicialObject.PInfty_comp_alexanderWhitney_comp_tensorHom_PInfty`: up to
  the projection onto normalized chains, the Alexander–Whitney map only depends on normalized
  chains.
* `CategoryTheory.Idempotents.DoldKan.oplaxMonoidalN`: the Alexander–Whitney oplax monoidal
  structure on the normalized chain functor `N`, with comultiplication
  `CategoryTheory.Idempotents.DoldKan.N_δ` and counit `CategoryTheory.Idempotents.DoldKan.N_η`.
* `CategoryTheory.Idempotents.DoldKan.laxMonoidalΓ`: the induced lax monoidal structure on the
  Dold–Kan functor `Γ`, with unit `CategoryTheory.Idempotents.DoldKan.Γ_ε` and tensorator
  `CategoryTheory.Idempotents.DoldKan.Γ_μ`.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Section 8.5.
* S. Schwede and B. Shipley, *Equivalences of monoidal model categories*, Algebr. Geom. Topol. 3
  (2003).
* J. Lurie, *Higher Algebra*, Construction 1.3.1.13.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology AlgebraicTopology.DoldKan
  Idempotents Opposite HomologicalComplex

open scoped Simplicial

universe v u

namespace CategoryTheory.SimplicialObject

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasFiniteCoproducts C] (A B : SimplicialObject C)

/-- The Alexander–Whitney map of a degenerate simplex of `A ⊗ B` vanishes on normalized chains:
in each summand, either the front face of `A` or the back face of `B` contains the collapsed
edge, so it is degenerate and is killed by `PInfty`. -/
private lemma σ_comp_alexanderWhitney_f_comp_tensorHom_PInfty_f (n : ℕ) (i : Fin (n + 1)) :
    (A ⊗ B).σ i ≫ (alexanderWhitney A B).f (n + 1) ≫
      (PInfty (X := A) ⊗ₘ PInfty (X := B)).f (n + 1) = 0 := by
  rw [alexanderWhitney_f]
  -- the summands are typed by the degreewise objects `A _⦋n + 1⦌ ⊗ B _⦋n + 1⦌`, so the objects of
  -- the alternating face map complexes are unfolded before the sums are distributed
  dsimp only [alternatingFaceMapComplex_obj_X, Monoidal.tensorObj_obj, SimplicialObject.σ,
    Monoidal.tensorObj_map]
  simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
  refine Finset.sum_eq_zero fun p _ ↦ ?_
  rw [tensorHom_eq_mapBifunctorMap, ι_tensorHom]
  simp only [tensorHom_comp_tensorHom_assoc, ← Functor.map_comp_assoc, ← op_comp]
  by_cases hip : (i : ℕ) < p
  · rw [degeneracy_comp_PInfty A _ _
      (SimplexCategory.not_mono_subinterval_comp_σ _ i (by omega) (by omega)),
      MonoidalPreadditive.zero_tensor, zero_comp]
  · rw [degeneracy_comp_PInfty B _ _
      (SimplexCategory.not_mono_subinterval_comp_σ _ i (by omega) (by omega)),
      MonoidalPreadditive.tensor_zero, zero_comp]

/-- **The Alexander–Whitney map preserves degenerate chains**: composed with the projection
`PInfty ⊗ PInfty` onto normalized chains, it vanishes on the degenerate part `QInfty` of the
chains of `A ⊗ B`. -/
@[reassoc]
lemma QInfty_comp_alexanderWhitney_comp_tensorHom_PInfty :
    QInfty ≫ alexanderWhitney A B ≫ (PInfty ⊗ₘ PInfty) = 0 := by
  ext n : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.zero_f,
    ← degeneraciesVanish_iff_QInfty_f_comp]
  cases n with
  | zero => exact (degeneraciesVanish_zero_iff_true _).2 trivial
  | succ n =>
    exact (degeneraciesVanish_succ_iff _).2
      (σ_comp_alexanderWhitney_f_comp_tensorHom_PInfty_f A B n)

/-- The Alexander–Whitney map followed by the projection `PInfty ⊗ PInfty` onto normalized chains
only depends on the normalized part of the chains of `A ⊗ B`. -/
@[reassoc]
lemma PInfty_comp_alexanderWhitney_comp_tensorHom_PInfty :
    PInfty ≫ alexanderWhitney A B ≫ (PInfty ⊗ₘ PInfty) =
      alexanderWhitney A B ≫ (PInfty ⊗ₘ PInfty) := by
  have h := congrArg (· ≫ alexanderWhitney A B ≫ (PInfty ⊗ₘ PInfty))
    (PInfty_add_QInfty (X := A ⊗ B))
  simp only [Preadditive.add_comp, QInfty_comp_alexanderWhitney_comp_tensorHom_PInfty,
    add_zero] at h
  exact h.trans (Category.id_comp _)

variable (C) in
/-- The projection `PInfty` onto normalized chains does not change the counit of the alternating
face map complex functor, which lives in degree zero where `PInfty` is the identity. -/
lemma PInfty_comp_η_alternatingFaceMapComplex :
    PInfty ≫ Functor.OplaxMonoidal.η (alternatingFaceMapComplex C) =
      Functor.OplaxMonoidal.η (alternatingFaceMapComplex C) := by
  ext (_ | n) : 1
  · rw [HomologicalComplex.comp_f, PInfty_f_0, Category.id_comp]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ (n + 1) (by omega)).eq_of_tgt _ _

end CategoryTheory.SimplicialObject

namespace CategoryTheory.Idempotents.DoldKan

variable {C : Type u} [Category.{v} C] [Preadditive C] [IsIdempotentComplete C]
  [HasFiniteCoproducts C]

omit [HasFiniteCoproducts C] in
/-- The counit of `toKaroubiEquivalence` at `N₁.obj X` lands in the summand cut out by
`PInfty`. -/
private lemma counitIso_hom_app_N₁_obj_f_comp_PInfty (X : SimplicialObject C) :
    ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.hom.app (N₁.obj X)).f ≫ PInfty =
      ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.hom.app (N₁.obj X)).f := by
  have h := Karoubi.comp_p ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.hom.app (N₁.obj X))
  simp only [Functor.id_obj, N₁_obj_p] at h
  exact h

omit [HasFiniteCoproducts C] in
/-- The inverse counit of `toKaroubiEquivalence` at `N₁.obj X` only depends on the summand cut
out by `PInfty`. -/
private lemma PInfty_comp_counitIso_inv_app_N₁_obj_f (X : SimplicialObject C) :
    PInfty ≫ ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.inv.app (N₁.obj X)).f =
      ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.inv.app (N₁.obj X)).f := by
  have h := Karoubi.p_comp ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.inv.app (N₁.obj X))
  simp only [Functor.id_obj, N₁_obj_p] at h
  exact h

/-- The inclusion of the normalized chains `N X` of the pseudoabelian Dold–Kan correspondence
into the alternating face map complex of `X`, as the direct summand cut out by `PInfty`.

By definition `N = N₁ ⋙ (toKaroubiEquivalence _).inverse`, so `N.obj X` is the object of chain
complexes corresponding to the formal direct summand `N₁.obj X` of the Karoubi envelope, whose
underlying complex is the alternating face map complex of `X` with idempotent `PInfty`
(`AlgebraicTopology.DoldKan.N₁_obj_p`); the counit of `toKaroubiEquivalence` identifies the two.
-/
def inclusionN : (N : SimplicialObject C ⥤ _) ⟶ alternatingFaceMapComplex C where
  app X := ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.hom.app (N₁.obj X)).f
  naturality X Y f := by
    have h := congrArg Karoubi.Hom.f
      ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.hom.naturality (N₁.map f))
    simp only [Karoubi.comp_f, Functor.comp_map, Functor.id_map, N₁_map_f,
      reassoc_of% (counitIso_hom_app_N₁_obj_f_comp_PInfty X)] at h
    exact h

/-- The projection of the alternating face map complex of `X` onto the normalized chains `N X`
of the pseudoabelian Dold–Kan correspondence. -/
def PInftyToN : alternatingFaceMapComplex C ⟶ (N : SimplicialObject C ⥤ _) where
  app X := ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.inv.app (N₁.obj X)).f
  naturality X Y f := by
    have h := congrArg Karoubi.Hom.f
      ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.inv.naturality (N₁.map f))
    have hn : PInfty ≫ AlternatingFaceMapComplex.map f =
        AlternatingFaceMapComplex.map f ≫ PInfty := by
      have h := ((natTransPInfty C).naturality f).symm
      simp only [natTransPInfty_app] at h
      exact h
    simp only [Karoubi.comp_f, Functor.comp_map, Functor.id_map, N₁_map_f, hn, Category.assoc,
      PInfty_comp_counitIso_inv_app_N₁_obj_f Y] at h
    exact h

private lemma inclusionN_app (X : SimplicialObject C) :
    inclusionN.app X = ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.hom.app (N₁.obj X)).f :=
  rfl

private lemma PInftyToN_app (X : SimplicialObject C) :
    PInftyToN.app X = ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.inv.app (N₁.obj X)).f :=
  rfl

/-- The normalized chains are a retract of the alternating face map complex. -/
@[reassoc (attr := simp)]
lemma inclusionN_app_comp_PInftyToN_app (X : SimplicialObject C) :
    inclusionN.app X ≫ PInftyToN.app X = 𝟙 (N.obj X) := by
  rw [inclusionN_app, PInftyToN_app]
  have h := congrArg Karoubi.Hom.f
    ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.hom_inv_id_app (N₁.obj X))
  simp only [Karoubi.comp_f, Karoubi.id_f, Functor.comp_obj, toKaroubiEquivalence,
    Functor.asEquivalence_functor, toKaroubi_obj_p] at h
  exact h

/-- The idempotent of the alternating face map complex cutting out the normalized chains is
`PInfty`. -/
@[reassoc (attr := simp)]
lemma PInftyToN_app_comp_inclusionN_app (X : SimplicialObject C) :
    PInftyToN.app X ≫ inclusionN.app X = PInfty := by
  rw [inclusionN_app, PInftyToN_app]
  have h := congrArg Karoubi.Hom.f
    ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.inv_hom_id_app (N₁.obj X))
  simp only [Karoubi.comp_f, Karoubi.id_f, Functor.id_obj, N₁_obj_p] at h
  exact h

/-- The projection onto normalized chains is unchanged by first applying `PInfty`. -/
@[reassoc (attr := simp)]
lemma PInfty_comp_PInftyToN_app (X : SimplicialObject C) :
    PInfty ≫ PInftyToN.app X = PInftyToN.app X :=
  PInfty_comp_counitIso_inv_app_N₁_obj_f X

/-- Normalized chains are fixed by `PInfty`. -/
@[reassoc (attr := simp)]
lemma inclusionN_app_comp_PInfty (X : SimplicialObject C) :
    inclusionN.app X ≫ PInfty = inclusionN.app X :=
  counitIso_hom_app_N₁_obj_f_comp_PInfty X

/-- The normalized chain functor is a retract of the alternating face map complex functor, with
inclusion `CategoryTheory.Idempotents.DoldKan.inclusionN` and projection
`CategoryTheory.Idempotents.DoldKan.PInftyToN`. -/
def retractN : Retract (N : SimplicialObject C ⥤ _) (alternatingFaceMapComplex C) where
  i := inclusionN
  r := PInftyToN
  retract := by
    ext X : 2
    exact inclusionN_app_comp_PInftyToN_app X

/-- The inclusion of the normalized chains retract. -/
@[simp]
lemma retractN_i : (retractN (C := C)).i = inclusionN :=
  (rfl)

/-- The projection of the normalized chains retract. -/
@[simp]
lemma retractN_r : (retractN (C := C)).r = PInftyToN :=
  (rfl)

section Monoidal

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable [MonoidalCategory C] [MonoidalPreadditive C]

/-- **The Alexander–Whitney oplax monoidal structure on normalized chains**: the normalized
chain functor `N` of the Dold–Kan correspondence is oplax monoidal, with comultiplication the
Alexander–Whitney map restricted to normalized chains and projected back onto them
(`CategoryTheory.Idempotents.DoldKan.N_δ`), and counit the counit of the alternating face map
complex (the identity of `𝟙_ C` in degree zero) restricted to normalized chains
(`CategoryTheory.Idempotents.DoldKan.N_η`). -/
@[no_expose]
instance oplaxMonoidalN : (N : SimplicialObject C ⥤ _).OplaxMonoidal :=
  Functor.OplaxMonoidal.ofRetract retractN
    (fun X Y ↦ by
      -- `PInfty ⊗ PInfty` is absorbed by the projection `PInftyToN ⊗ PInftyToN`
      simpa [tensorHom_comp_tensorHom] using
        SimplicialObject.PInfty_comp_alexanderWhitney_comp_tensorHom_PInfty_assoc X Y
          (PInftyToN.app X ⊗ₘ PInftyToN.app Y))
    (by rw [retractN_i, retractN_r, PInftyToN_app_comp_inclusionN_app_assoc,
      SimplicialObject.PInfty_comp_η_alternatingFaceMapComplex])

/-- The comultiplication of the normalized chain functor: the Alexander–Whitney map of the
alternating face map complexes, restricted to and projected onto normalized chains. -/
@[simp]
lemma N_δ (X Y : SimplicialObject C) :
    Functor.OplaxMonoidal.δ N X Y = inclusionN.app (X ⊗ Y) ≫
      SimplicialObject.alexanderWhitney X Y ≫ (PInftyToN.app X ⊗ₘ PInftyToN.app Y) :=
  (Functor.OplaxMonoidal.ofRetract_δ _ _ _ X Y).trans (by
    rw [SimplicialObject.alternatingFaceMapComplex_δ, retractN_i, retractN_r])

/-- The counit of the normalized chain functor: the counit of the alternating face map complex,
the identity of `𝟙_ C` in degree zero, restricted to normalized chains. -/
@[simp]
lemma N_η :
    Functor.OplaxMonoidal.η (N : SimplicialObject C ⥤ _) =
      inclusionN.app (𝟙_ _) ≫ Functor.OplaxMonoidal.η (alternatingFaceMapComplex C) :=
  Functor.OplaxMonoidal.ofRetract_η _ _ _

/-- On normalized chains, the comultiplication of `N` is the Alexander–Whitney map followed by
the projection onto normalized chains. -/
@[reassoc]
lemma N_δ_comp_tensorHom_inclusionN_app (X Y : SimplicialObject C) :
    Functor.OplaxMonoidal.δ N X Y ≫ (inclusionN.app X ⊗ₘ inclusionN.app Y) =
      inclusionN.app (X ⊗ Y) ≫ SimplicialObject.alexanderWhitney X Y ≫ (PInfty ⊗ₘ PInfty) := by
  rw [N_δ, Category.assoc, Category.assoc, tensorHom_comp_tensorHom,
    PInftyToN_app_comp_inclusionN_app, PInftyToN_app_comp_inclusionN_app]

/-- **The lax monoidal structure of the Dold–Kan functor** `Γ` from chain complexes to
simplicial objects: it is the mate, along the Dold–Kan equivalence, of the Alexander–Whitney
oplax monoidal structure of the normalized chain functor `N`
(`CategoryTheory.Idempotents.DoldKan.Γ_ε` and `CategoryTheory.Idempotents.DoldKan.Γ_μ`). -/
@[no_expose]
instance laxMonoidalΓ : (Γ : ChainComplex C ℕ ⥤ _).LaxMonoidal :=
  letI : (equivalence (C := C)).functor.OplaxMonoidal := oplaxMonoidalN
  (equivalence (C := C)).toAdjunction.rightAdjointLaxMonoidal

/-- The unit of the lax monoidal functor `Γ` is the transpose of the counit of `N` along the
Dold–Kan equivalence. -/
lemma Γ_ε :
    Functor.LaxMonoidal.ε (Γ : ChainComplex C ℕ ⥤ _) =
      (equivalence (C := C)).unit.app (𝟙_ _) ≫ Γ.map (Functor.OplaxMonoidal.η N) :=
  -- `laxMonoidalΓ` is `rightAdjointLaxMonoidal` for the Dold–Kan equivalence, whose functor is
  -- `N` and inverse is `Γ` (`equivalence_functor`, `equivalence_inverse`)
  letI : (equivalence (C := C)).functor.OplaxMonoidal := oplaxMonoidalN
  equivalence.toAdjunction.rightAdjointLaxMonoidal_ε.trans
    (equivalence.toAdjunction.homEquiv_unit _ _ _)

/-- The tensorator of the lax monoidal functor `Γ` is the transpose of the comultiplication of
`N` along the Dold–Kan equivalence. -/
lemma Γ_μ (K L : ChainComplex C ℕ) :
    Functor.LaxMonoidal.μ (Γ : ChainComplex C ℕ ⥤ _) K L =
      (equivalence (C := C)).unit.app (Γ.obj K ⊗ Γ.obj L) ≫
        Γ.map (Functor.OplaxMonoidal.δ N (Γ.obj K) (Γ.obj L) ≫
          ((equivalence (C := C)).counit.app K ⊗ₘ (equivalence (C := C)).counit.app L)) :=
  letI : (equivalence (C := C)).functor.OplaxMonoidal := oplaxMonoidalN
  (equivalence.toAdjunction.rightAdjointLaxMonoidal_μ K L).trans
    (equivalence.toAdjunction.homEquiv_unit _ _ _)

end Monoidal

end CategoryTheory.Idempotents.DoldKan
