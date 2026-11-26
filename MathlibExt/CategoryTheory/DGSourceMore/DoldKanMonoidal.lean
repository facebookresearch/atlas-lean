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
# Monoidal structures in the Dold–Kan correspondence

Let `C` be preadditive and idempotent complete with finite coproducts,
and monoidal with biadditive tensor. Its Dold–Kan equivalence has
normalized-chain functor `N` and inverse `Γ`. The normalization
idempotent `P∞` on alternating-face chains splits through natural
maps `i : N → C_*`, `p : C_* → N`, with `i ≫ p=id_N` and `p ≫ i=P∞`.

The Alexander–Whitney map followed by `P∞ ⊗ P∞` annihilates the
degenerate complement. It therefore gives the oplax structure
`N(A ⊗ B) → N(A) ⊗ N(B)`, with counit restricted from alternating-face
chains. Its mate under `N ⊣ Γ` gives the lax structure
`Γ(K) ⊗ Γ(L) → Γ(K ⊗ L)`. These constructions use no abelian-category
hypothesis.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Section 8.5.
* S. Schwede and B. Shipley, *Equivalences of monoidal model categories*, Algebr. Geom. Topol. 3 (2003).
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

/-- Let `C` be preadditive and monoidal with biadditive tensor and
finite coproducts, and `A,B` simplicial objects. Write `P∞` for the
normalization idempotent on alternating-face chains and `Q∞=1-P∞`
for its degenerate complement. The composite `Q∞_(A⊗B) ≫ AW_(A,B) ≫ (P∞_A ⊗ P∞_B)`
is zero: each Alexander–Whitney summand of a degenerate simplex
has a degenerate front or back face. -/
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

/-- Let `C` be preadditive and monoidal with biadditive tensor and
finite coproducts, and `A,B` simplicial objects. Write `P∞` for the
normalization idempotent on alternating-face chains and `Q∞=1-P∞`
for its degenerate complement. The equality
`P∞_(A⊗B) ≫ AW_(A,B) ≫ (P∞_A ⊗ P∞_B) = AW_(A,B) ≫ (P∞_A ⊗ P∞_B)`
shows that the projected Alexander–Whitney map depends only on the
normalized source part. -/
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
/-- Let `C` be preadditive and monoidal with biadditive tensor and
finite coproducts. On the constant simplicial unit, the normalization
idempotent `P∞` followed by the alternating-face-chain counit equals
that counit, since its nonzero component is in degree zero. -/
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

/- N is obtained from N₁ through the inverse Karoubi equivalence; its counit identifies the underlying alternating-face complex with the idempotent summand. -/

/-- Let `C` be preadditive and idempotent complete with finite
coproducts. The normalized Dold–Kan chain functor has a natural
inclusion `N(X) → C_*(X)` whose image is the direct summand cut out
by the normalization idempotent `P∞`. -/
def inclusionN : (N : SimplicialObject C ⥤ _) ⟶ alternatingFaceMapComplex C where
  app X := ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.hom.app (N₁.obj X)).f
  naturality X Y f := by
    have h := congrArg Karoubi.Hom.f
      ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.hom.naturality (N₁.map f))
    simp only [Karoubi.comp_f, Functor.comp_map, Functor.id_map, N₁_map_f,
      reassoc_of% (counitIso_hom_app_N₁_obj_f_comp_PInfty X)] at h
    exact h

/-- Let `C` be preadditive and idempotent complete with finite
coproducts. The alternating-face chain functor has a natural
projection `C_*(X) → N(X)` onto its summand defined by `P∞`. -/
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

/-- Let `C` be preadditive, idempotent complete, and have finite
coproducts. Let `N` be its normalized Dold–Kan chain functor,
`C_*` the alternating-face chain functor, `i : N → C_*` the
inclusion and `p : C_* → N` the projection. For every simplicial `X`, inclusion followed by projection
is the identity of `N(X)`: `i_X ≫ p_X=𝟙 N(X)`. -/
@[reassoc (attr := simp)]
lemma inclusionN_app_comp_PInftyToN_app (X : SimplicialObject C) :
    inclusionN.app X ≫ PInftyToN.app X = 𝟙 (N.obj X) := by
  rw [inclusionN_app, PInftyToN_app]
  have h := congrArg Karoubi.Hom.f
    ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.hom_inv_id_app (N₁.obj X))
  simp only [Karoubi.comp_f, Karoubi.id_f, Functor.comp_obj, toKaroubiEquivalence,
    Functor.asEquivalence_functor, toKaroubi_obj_p] at h
  exact h

/-- Let `C` be preadditive, idempotent complete, and have finite
coproducts. Let `N` be its normalized Dold–Kan chain functor,
`C_*` the alternating-face chain functor, `i : N → C_*` the
inclusion and `p : C_* → N` the projection. For every simplicial `X`, projection followed by inclusion
is the normalization idempotent on `C_*(X)`: `p_X ≫ i_X=P∞`. -/
@[reassoc (attr := simp)]
lemma PInftyToN_app_comp_inclusionN_app (X : SimplicialObject C) :
    PInftyToN.app X ≫ inclusionN.app X = PInfty := by
  rw [inclusionN_app, PInftyToN_app]
  have h := congrArg Karoubi.Hom.f
    ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.inv_hom_id_app (N₁.obj X))
  simp only [Karoubi.comp_f, Karoubi.id_f, Functor.id_obj, N₁_obj_p] at h
  exact h

/-- Let `C` be preadditive, idempotent complete, and have finite
coproducts. Let `N` be its normalized Dold–Kan chain functor,
`C_*` the alternating-face chain functor, `i : N → C_*` the
inclusion and `p : C_* → N` the projection. For every simplicial `X`, applying `P∞` before the
projection to `N(X)` leaves that projection unchanged: `P∞ ≫ p_X=p_X`. -/
@[reassoc (attr := simp)]
lemma PInfty_comp_PInftyToN_app (X : SimplicialObject C) :
    PInfty ≫ PInftyToN.app X = PInftyToN.app X :=
  PInfty_comp_counitIso_inv_app_N₁_obj_f X

/-- Let `C` be preadditive, idempotent complete, and have finite
coproducts. Let `N` be its normalized Dold–Kan chain functor,
`C_*` the alternating-face chain functor, `i : N → C_*` the
inclusion and `p : C_* → N` the projection. For every simplicial `X`, applying `P∞` after the inclusion
of `N(X)` leaves that inclusion unchanged: `i_X ≫ P∞=i_X`. -/
@[reassoc (attr := simp)]
lemma inclusionN_app_comp_PInfty (X : SimplicialObject C) :
    inclusionN.app X ≫ PInfty = inclusionN.app X :=
  counitIso_hom_app_N₁_obj_f_comp_PInfty X

/-- Let `C` be preadditive, idempotent complete, and have finite
coproducts. Let `N` be its normalized Dold–Kan chain functor,
`C_*` the alternating-face chain functor, `i : N → C_*` the
inclusion and `p : C_* → N` the projection. The natural inclusion and projection exhibit `N` as a
retract of the alternating-face chain functor in the category of
functors from simplicial objects to nonnegative chain complexes. -/
def retractN : Retract (N : SimplicialObject C ⥤ _) (alternatingFaceMapComplex C) where
  i := inclusionN
  r := PInftyToN
  retract := by
    ext X : 2
    exact inclusionN_app_comp_PInftyToN_app X

/-- Let `C` be preadditive, idempotent complete, and have finite
coproducts. Let `N` be its normalized Dold–Kan chain functor,
`C_*` the alternating-face chain functor, `i : N → C_*` the
inclusion and `p : C_* → N` the projection. The inclusion map of the normalized-chain functor retract
is the natural transformation `i : N → C_*`. -/
@[simp]
lemma retractN_i : (retractN (C := C)).i = inclusionN :=
  (rfl)

/-- Let `C` be preadditive, idempotent complete, and have finite
coproducts. Let `N` be its normalized Dold–Kan chain functor,
`C_*` the alternating-face chain functor, `i : N → C_*` the
inclusion and `p : C_* → N` the projection. The retraction map of the normalized-chain functor retract
is the natural transformation `p : C_* → N`. -/
@[simp]
lemma retractN_r : (retractN (C := C)).r = PInftyToN :=
  (rfl)

section Monoidal

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable [MonoidalCategory C] [MonoidalPreadditive C]

/-- Let `C` be preadditive, idempotent complete, and have finite
coproducts. Let `N` be its normalized Dold–Kan chain functor,
`C_*` the alternating-face chain functor, `i : N → C_*` the
inclusion and `p : C_* → N` the projection. Suppose `C` is monoidal with biadditive tensor. The Alexander–Whitney map descends to an oplax monoidal
structure on `N`, with tensor comparison obtained by inclusion,
Alexander–Whitney, and projection, and counit restricted from `C_*`. -/
@[no_expose]
instance oplaxMonoidalN : (N : SimplicialObject C ⥤ _).OplaxMonoidal :=
  Functor.OplaxMonoidal.ofRetract retractN
    (fun X Y ↦ by
      -- `PInfty ⊗ PInfty` is absorbed by the projection `PInftyToN ⊗ PInftyToN`
      simpa [MonoidalCategory.tensorHom_comp_tensorHom] using
        SimplicialObject.PInfty_comp_alexanderWhitney_comp_tensorHom_PInfty_assoc X Y
          (PInftyToN.app X ⊗ₘ PInftyToN.app Y))
    (by rw [retractN_i, retractN_r, PInftyToN_app_comp_inclusionN_app_assoc,
      SimplicialObject.PInfty_comp_η_alternatingFaceMapComplex])

/-- Let `C` be preadditive, idempotent complete, and have finite
coproducts. Let `N` be its normalized Dold–Kan chain functor,
`C_*` the alternating-face chain functor, `i : N → C_*` the
inclusion and `p : C_* → N` the projection. Suppose `C` is monoidal with biadditive tensor. For simplicial `X,Y`, the normalized tensor comparison is
`δ_N(X,Y) = i_(X⊗Y) ≫ AW_(X,Y) ≫ (p_X ⊗ p_Y)`. -/
@[simp]
lemma N_δ (X Y : SimplicialObject C) :
    Functor.OplaxMonoidal.δ N X Y = inclusionN.app (X ⊗ Y) ≫
      SimplicialObject.alexanderWhitney X Y ≫ (PInftyToN.app X ⊗ₘ PInftyToN.app Y) :=
  (Functor.OplaxMonoidal.ofRetract_δ _ _ _ X Y).trans (by
    rw [SimplicialObject.alternatingFaceMapComplex_δ, retractN_i, retractN_r])

/-- Let `C` be preadditive, idempotent complete, and have finite
coproducts. Let `N` be its normalized Dold–Kan chain functor,
`C_*` the alternating-face chain functor, `i : N → C_*` the
inclusion and `p : C_* → N` the projection. Suppose `C` is monoidal with biadditive tensor. The normalized counit is
`η_N = i_(𝟙_Simp) ≫ η_(C_*)`, the restriction of the alternating-
face-chain counit to the normalized summand. -/
@[simp]
lemma N_η :
    Functor.OplaxMonoidal.η (N : SimplicialObject C ⥤ _) =
      inclusionN.app (𝟙_ _) ≫ Functor.OplaxMonoidal.η (alternatingFaceMapComplex C) :=
  Functor.OplaxMonoidal.ofRetract_η _ _ _

/-- Let `C` be preadditive, idempotent complete, and have finite
coproducts. Let `N` be its normalized Dold–Kan chain functor,
`C_*` the alternating-face chain functor, `i : N → C_*` the
inclusion and `p : C_* → N` the projection. Suppose `C` is monoidal with biadditive tensor. For simplicial `X,Y`, inclusion of both target normalized
factors gives
`δ_N(X,Y) ≫ (i_X ⊗ i_Y) = i_(X⊗Y) ≫ AW_(X,Y) ≫ (P∞_X ⊗ P∞_Y)`. -/
@[reassoc]
lemma N_δ_comp_tensorHom_inclusionN_app (X Y : SimplicialObject C) :
    Functor.OplaxMonoidal.δ N X Y ≫ (inclusionN.app X ⊗ₘ inclusionN.app Y) =
      inclusionN.app (X ⊗ Y) ≫ SimplicialObject.alexanderWhitney X Y ≫ (PInfty ⊗ₘ PInfty) := by
  rw [N_δ, Category.assoc, Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
    PInftyToN_app_comp_inclusionN_app, PInftyToN_app_comp_inclusionN_app]

/-- Let `C` be preadditive, idempotent complete, and monoidal with
biadditive tensor and finite coproducts. Let `N` and `Γ` be the
normalized-chain and inverse functors of the Dold–Kan equivalence. The mate of the Alexander–Whitney oplax structure on `N`
under `N ⊣ Γ` is a lax monoidal structure on `Γ`, with unit
`𝟙_Simp → Γ(𝟙_Chain)` and tensorator
`Γ(K) ⊗ Γ(L) → Γ(K ⊗ L)`. -/
@[no_expose]
instance laxMonoidalΓ : (Γ : ChainComplex C ℕ ⥤ _).LaxMonoidal :=
  letI : (equivalence (C := C)).functor.OplaxMonoidal := oplaxMonoidalN
  (equivalence (C := C)).toAdjunction.rightAdjointLaxMonoidal

/-- Let `C` be preadditive, idempotent complete, and monoidal with
biadditive tensor and finite coproducts. Let `N` and `Γ` be the
normalized-chain and inverse functors of the Dold–Kan equivalence. The lax unit of `Γ` is the equivalence unit at the simplicial
tensor unit followed by `Γ` of the normalized-chain counit `η_N`. -/
lemma Γ_ε :
    Functor.LaxMonoidal.ε (Γ : ChainComplex C ℕ ⥤ _) =
      (equivalence (C := C)).unit.app (𝟙_ _) ≫ Γ.map (Functor.OplaxMonoidal.η N) :=
  -- `laxMonoidalΓ` is `rightAdjointLaxMonoidal` for the Dold–Kan equivalence, whose functor is
  -- `N` and inverse is `Γ` (`equivalence_functor`, `equivalence_inverse`)
  letI : (equivalence (C := C)).functor.OplaxMonoidal := oplaxMonoidalN
  equivalence.toAdjunction.rightAdjointLaxMonoidal_ε.trans
    (equivalence.toAdjunction.homEquiv_unit _ _ _)

/-- Let `C` be preadditive, idempotent complete, and monoidal with
biadditive tensor and finite coproducts. Let `N` and `Γ` be the
normalized-chain and inverse functors of the Dold–Kan equivalence. For chain complexes `K,L`, the lax tensorator of `Γ` is
the equivalence unit at `Γ(K) ⊗ Γ(L)`, followed by `Γ` of
`δ_N(Γ(K),Γ(L))` and then the tensor of the equivalence counits
`NΓ(K) → K`, `NΓ(L) → L`. -/
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
