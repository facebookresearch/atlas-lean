/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Authors: @toskua, Avocado
module
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import MathlibExt.Algebra.Homology.HomComplex.CocycleBoundary
public import MathlibExt.CategoryTheory.Abelian.RightDerived.HorseshoeExtendedDiagram

/-!
# Boundary representatives for degreewise split sequences

For S=(A→B→D) split at each cochain degree, choose sections s_q and
retractions r_q. A cycle f:Z→D^q lifts to u_q=f s_q in B^q, and its
connecting representative is ρ_q=u_q d_B^q r_{q+1} in A^{q+1}.

The pair (−ρ_q,u_q) is the corresponding cone cocycle. Its descent returns
f, and its cone-triangle boundary returns ρ_q. The same representative
computes both the homology connecting map and the derived short-exact
triangle connector under the stated hypotheses.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace HomologicalComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

/--
Let C be an abelian category and S=(A→B→D) a short complex of natural cochain complexes, split
at every degree. Write rₙ:Bⁿ→Aⁿ and sₙ:Dⁿ→Bⁿ for the retraction and section of the degree-n
splitting. For any object Z, degree n∈ℕ and morphism f:Z→Dⁿ, the section lift to Bⁿ is u=f≫sₙ.
No cocycle hypothesis on f is needed to define this lift.
-/
def splitCycleLift (S : ShortComplex (CochainComplex C ℕ))
    (s : ∀ n : ℕ, (S.map (eval C (.up ℕ) n)).Splitting)
    {Z : C} (n : ℕ) (f : Z ⟶ S.X₃.X n) : Z ⟶ S.X₂.X n :=
  f ≫ (s n).s

/--
Let C be an abelian category and S=(A→B→D) a short complex of natural cochain complexes, split
at every degree. Write rₙ:Bⁿ→Aⁿ and sₙ:Dⁿ→Bⁿ for the retraction and section of the degree-n
splitting. For f:Z→Dⁿ, the connecting representative in Aⁿ⁺¹ is ρ=f≫sₙ≫d_Bⁿ≫r_{n+1}. It uses
the middle differential and the next degree's retraction.
-/
def splitConnectingRepresentative (S : ShortComplex (CochainComplex C ℕ))
    (s : ∀ n : ℕ, (S.map (eval C (.up ℕ) n)).Splitting)
    {Z : C} (n : ℕ) (f : Z ⟶ S.X₃.X n) : Z ⟶ S.X₁.X (n + 1) :=
  splitCycleLift S s n f ≫ S.X₂.d n (n + 1) ≫ (s (n + 1)).r

theorem splitCycleLift_project (S : ShortComplex (CochainComplex C ℕ))
    (s : ∀ n : ℕ, (S.map (eval C (.up ℕ) n)).Splitting)
    {Z : C} (n : ℕ) (f : Z ⟶ S.X₃.X n) :
    splitCycleLift S s n f ≫ S.g.f n = f := by
  have h : (s n).s ≫ S.g.f n = 𝟙 _ := (s n).s_g
  exact (Category.assoc f (s n).s (S.g.f n)).trans
    ((congrArg (fun a => f ≫ a) h).trans (Category.comp_id f))

set_option backward.isDefEq.respectTransparency false in
theorem splitConnectingRepresentative_lift (S : ShortComplex (CochainComplex C ℕ))
    (s : ∀ n : ℕ, (S.map (eval C (.up ℕ) n)).Splitting)
    {Z : C} (n : ℕ) (f : Z ⟶ S.X₃.X n)
    (hf : f ≫ S.X₃.d n (n + 1) = 0) :
    splitConnectingRepresentative S s n f ≫ S.f.f (n + 1) =
      splitCycleLift S s n f ≫ S.X₂.d n (n + 1) := by
  have hp : (splitCycleLift S s n f ≫ S.X₂.d n (n + 1)) ≫ S.g.f (n + 1) = 0 := by
    rw [Category.assoc, ← S.g.comm, ← Category.assoc, splitCycleLift_project, hf]
  have hr : (s (n + 1)).r ≫ S.f.f (n + 1) =
      𝟙 _ - S.g.f (n + 1) ≫ (s (n + 1)).s := (s (n + 1)).r_f
  change (splitCycleLift S s n f ≫ S.X₂.d n (n + 1) ≫ (s (n + 1)).r) ≫
      S.f.f (n + 1) = _
  rw [Category.assoc, Category.assoc, hr]
  rw [Preadditive.comp_sub, Category.comp_id, Preadditive.comp_sub,
    ← Category.assoc, ← Category.assoc, hp, zero_comp, sub_zero]

set_option backward.isDefEq.respectTransparency false in
theorem splitConnectingRepresentative_cycle (S : ShortComplex (CochainComplex C ℕ))
    (s : ∀ n : ℕ, (S.map (eval C (.up ℕ) n)).Splitting)
    {Z : C} (n : ℕ) (f : Z ⟶ S.X₃.X n)
    (hf : f ≫ S.X₃.d n (n + 1) = 0) :
    splitConnectingRepresentative S s n f ≫ S.X₁.d (n + 1) (n + 2) = 0 := by
  have : Mono (S.f.f (n + 2)) := (s (n + 2)).mono_f
  apply (cancel_mono (S.f.f (n + 2))).mp
  rw [zero_comp, Category.assoc, ← S.f.comm, ← Category.assoc,
    splitConnectingRepresentative_lift S s n f hf, Category.assoc, S.X₂.d_comp_d, comp_zero]

end HomologicalComplex

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace HomologicalComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

/--
Let C be an abelian category and S=(A→B→D) a short complex of natural cochain complexes, split
at every degree. Write rₙ:Bⁿ→Aⁿ and sₙ:Dⁿ→Bⁿ for the retraction and section of the degree-n
splitting. The degreewise split short exact sequences make S a short exact sequence of cochain
complexes.
-/
theorem splitDiagram_shortExact (S : ShortComplex (CochainComplex C ℕ))
    (s : ∀ n : ℕ, (S.map (eval C (.up ℕ) n)).Splitting) : S.ShortExact := by
  apply shortExact_of_degreewise_shortExact
  exact fun n => (s n).shortExact

set_option backward.isDefEq.respectTransparency false in
/--
Let C be an abelian category and S=(A→B→D) a short complex of natural cochain complexes, split
at every degree. Write rₙ:Bⁿ→Aⁿ and sₙ:Dⁿ→Bⁿ for the retraction and section of the degree-n
splitting. Let j_D:Zⁿ(D)→Dⁿ and π_D:Zⁿ(D)→Hⁿ(D) be the cycle inclusion and quotient. The
connecting map satisfies π_D≫δ_S = π_A applied to the cycle represented by
j_D≫sₙ≫d_Bⁿ≫r_{n+1}, in degree n+1.
-/
theorem splitDiagram_delta_cycles (S : ShortComplex (CochainComplex C ℕ))
    (s : ∀ n : ℕ, (S.map (eval C (.up ℕ) n)).Splitting) (n : ℕ) :
    S.X₃.homologyπ n ≫ (splitDiagram_shortExact S s).δ n (n + 1) rfl =
      S.X₁.liftCycles (splitConnectingRepresentative S s n (S.X₃.iCycles n))
        (n + 2) (ComplexShape.next_eq' _ (ComplexShape.up_mk _ _ rfl))
        (splitConnectingRepresentative_cycle S s n (S.X₃.iCycles n)
          (S.X₃.iCycles_d n (n + 1))) ≫ S.X₁.homologyπ (n + 1) := by
  have h := (splitDiagram_shortExact S s).δ_eq n (n + 1) rfl
    (S.X₃.iCycles n) (S.X₃.iCycles_d n (n + 1))
    (splitCycleLift S s n (S.X₃.iCycles n))
    (splitCycleLift_project S s n (S.X₃.iCycles n))
    (splitConnectingRepresentative S s n (S.X₃.iCycles n))
    (splitConnectingRepresentative_lift S s n (S.X₃.iCycles n)
      (S.X₃.iCycles_d n (n + 1)))
    (n + 2) (ComplexShape.next_eq' _ (ComplexShape.up_mk _ _ rfl))
  have hi : S.X₃.liftCycles (S.X₃.iCycles n) (n + 1)
      (ComplexShape.next_eq' _ (ComplexShape.up_mk _ _ rfl))
      (S.X₃.iCycles_d n (n + 1)) = 𝟙 _ := by
    apply (cancel_mono (S.X₃.iCycles n)).mp
    rw [liftCycles_i, Category.id_comp]
  simpa only [Category.id_comp] using ((congrArg (fun a => a ≫ S.X₃.homologyπ n ≫
      (splitDiagram_shortExact S s).δ n (n + 1) rfl) hi).symm.trans h)

end HomologicalComplex

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace HomologicalComplex.SplitBoundary
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type*} {c : ComplexShape ι}

/--
Let C be an abelian category and S=(A→B→D) a short complex of complexes of shape c on ι, with
a splitting at each degree. Write rᵢ:Bᵢ→Aᵢ and sᵢ:Dᵢ→Bᵢ for its retractions and sections. For
an object Z and any f:Z→Dᵢ, the chosen degreewise lift is f≫sᵢ:Z→Bᵢ.
-/
def cycleLift (S : ShortComplex (HomologicalComplex C c))
    (s : ∀ i : ι, (S.map (eval C c i)).Splitting)
    {Z : C} (i : ι) (f : Z ⟶ S.X₃.X i) : Z ⟶ S.X₂.X i := f ≫ (s i).s

/--
Let C be an abelian category and S=(A→B→D) a short complex of complexes of shape c on ι, with
a splitting at each degree. Write rᵢ:Bᵢ→Aᵢ and sᵢ:Dᵢ→Bᵢ for its retractions and sections. For
indices i,j and f:Z→Dᵢ, the representative in Aⱼ is f≫sᵢ≫B.d i j≫rⱼ. It is zero on disallowed
differential pairs because B.d i j is zero there.
-/
def representative (S : ShortComplex (HomologicalComplex C c))
    (s : ∀ i : ι, (S.map (eval C c i)).Splitting)
    {Z : C} (i j : ι) (f : Z ⟶ S.X₃.X i) : Z ⟶ S.X₁.X j :=
  cycleLift S s i f ≫ S.X₂.d i j ≫ (s j).r

theorem cycleLift_project (S : ShortComplex (HomologicalComplex C c))
    (s : ∀ i : ι, (S.map (eval C c i)).Splitting)
    {Z : C} (i : ι) (f : Z ⟶ S.X₃.X i) : cycleLift S s i f ≫ S.g.f i = f := by
  have h : (s i).s ≫ S.g.f i = 𝟙 _ := (s i).s_g
  exact (Category.assoc f (s i).s (S.g.f i)).trans
    ((congrArg (fun a => f ≫ a) h).trans (Category.comp_id f))

set_option backward.isDefEq.respectTransparency false in
theorem representative_lift (S : ShortComplex (HomologicalComplex C c))
    (s : ∀ i : ι, (S.map (eval C c i)).Splitting)
    {Z : C} (i j : ι) (f : Z ⟶ S.X₃.X i) (hf : f ≫ S.X₃.d i j = 0) :
    representative S s i j f ≫ S.f.f j = cycleLift S s i f ≫ S.X₂.d i j := by
  have hp : (cycleLift S s i f ≫ S.X₂.d i j) ≫ S.g.f j = 0 := by
    rw [Category.assoc, ← S.g.comm, ← Category.assoc, cycleLift_project, hf]
  have hr : (s j).r ≫ S.f.f j = 𝟙 _ - S.g.f j ≫ (s j).s := (s j).r_f
  change (cycleLift S s i f ≫ S.X₂.d i j ≫ (s j).r) ≫ S.f.f j = _
  rw [Category.assoc, Category.assoc, hr]
  rw [Preadditive.comp_sub, Category.comp_id, Preadditive.comp_sub,
    ← Category.assoc, ← Category.assoc, hp, zero_comp, sub_zero]

set_option backward.isDefEq.respectTransparency false in
theorem representative_cycle (S : ShortComplex (HomologicalComplex C c))
    (s : ∀ i : ι, (S.map (eval C c i)).Splitting)
    {Z : C} (i j k : ι) (f : Z ⟶ S.X₃.X i) (hf : f ≫ S.X₃.d i j = 0) :
    representative S s i j f ≫ S.X₁.d j k = 0 := by
  have : Mono (S.f.f k) := (s k).mono_f
  apply (cancel_mono (S.f.f k)).mp
  rw [zero_comp, Category.assoc, ← S.f.comm, ← Category.assoc,
    representative_lift S s i j f hf, Category.assoc, S.X₂.d_comp_d, comp_zero]

end HomologicalComplex.SplitBoundary

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace HomologicalComplex.SplitBoundary
open CochainComplex.HomComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

/--
Let C be an abelian category and S=(A→B→D) a short complex of integer cochain complexes, split
degreewise with maps r_q:B^q→A^q and s_q:D^q→B^q. Fix an object Z, q∈ℤ and f:Z→D^q. Put
u_q=f≫s_q and ρ_q=u_q≫d_B^q≫r_{q+1}. If f≫d_D^q=0, then ρ_q is a cycle in A^{q+1}. It
determines a degree-(q+1) cocycle from the complex concentrated at Z in degree zero to A.
-/
def representativeCocycle (S : ShortComplex (CochainComplex C ℤ))
    (s : ∀ i : ℤ, (S.map (eval C (.up ℤ) i)).Splitting)
    {Z : C} (q : ℤ) (f : Z ⟶ S.X₃.X q) (hf : f ≫ S.X₃.d q (q + 1) = 0) :
    Cocycle ((CochainComplex.singleFunctor C 0).obj Z) S.X₁ (q + 1) :=
  Cocycle.fromSingleMk (representative S s q (q + 1) f) (zero_add _)
    (q + 2) (by omega) (representative_cycle S s q (q + 1) (q + 2) f hf)

/--
Let C be an abelian category and S=(A→B→D) a short complex of integer cochain complexes, split
degreewise with maps r_q:B^q→A^q and s_q:D^q→B^q. Fix an object Z, q∈ℤ and f:Z→D^q. Put
u_q=f≫s_q and ρ_q=u_q≫d_B^q≫r_{q+1}. The section lift u_q:Z→B^q determines a degree-q Hom
cochain from the complex concentrated at Z in degree zero to B, without requiring f to be
closed.
-/
def middleCochain (S : ShortComplex (CochainComplex C ℤ))
    (s : ∀ i : ℤ, (S.map (eval C (.up ℤ) i)).Splitting)
    {Z : C} (q : ℤ) (f : Z ⟶ S.X₃.X q) :
    Cochain ((CochainComplex.singleFunctor C 0).obj Z) S.X₂ q :=
  Cochain.fromSingleMk (cycleLift S s q f) (zero_add _)

set_option backward.isDefEq.respectTransparency false in
/--
Let C be an abelian category and S=(A→B→D) a short complex of integer cochain complexes, split
degreewise with r_q:B^q→A^q and s_q:D^q→B^q. Fix Z, q∈ℤ and f:Z→D^q. Put u_q=f≫s_q and
ρ_q=u_q≫d_B^q≫r_{q+1}. Assume f≫d_D^q=0. In the Hom complex from the complex Z[0] concentrated
at Z in degree zero, δ(u_q)+((−ρ_q)≫S.f)=0. The negative sign is the shifted-source coordinate
of the cone cocycle.
-/
theorem middleCochain_cone_relation (S : ShortComplex (CochainComplex C ℤ))
    (s : ∀ i : ℤ, (S.map (eval C (.up ℤ) i)).Splitting)
    {Z : C} (q : ℤ) (f : Z ⟶ S.X₃.X q) (hf : f ≫ S.X₃.d q (q + 1) = 0) :
    CochainComplex.HomComplex.δ q (q + 1) (middleCochain S s q f) +
      (-representativeCocycle S s q f hf).val.comp (Cochain.ofHom S.f) (add_zero _) = 0 := by
  change CochainComplex.HomComplex.δ q (q + 1)
      (Cochain.fromSingleMk (cycleLift S s q f) (zero_add q)) +
      (-(Cochain.fromSingleMk (representative S s q (q + 1) f) (zero_add (q + 1)))).comp
        (Cochain.ofHom S.f) (add_zero _) = 0
  rw [Cochain.δ_fromSingleMk, Cochain.neg_comp, ← Cochain.fromSingleMk_postcomp,
    representative_lift S s q (q + 1) f hf]
  exact add_neg_cancel _

/--
Let C be an abelian category and S=(A→B→D) a short complex of integer cochain complexes, split
degreewise with maps r_q:B^q→A^q and s_q:D^q→B^q. Fix an object Z, q∈ℤ and f:Z→D^q. Put
u_q=f≫s_q and ρ_q=u_q≫d_B^q≫r_{q+1}. If f is closed, the pair (−ρ_q,u_q) defines a degree-q
cocycle from Z[0] to Cone(S.f), with shifted A-coordinate −ρ_q and middle B-coordinate u_q.
-/
def originalConeCocycle (S : ShortComplex (CochainComplex C ℤ))
    (s : ∀ i : ℤ, (S.map (eval C (.up ℤ) i)).Splitting)
    {Z : C} (q : ℤ) (f : Z ⟶ S.X₃.X q) (hf : f ≫ S.X₃.d q (q + 1) = 0) :
    Cocycle ((CochainComplex.singleFunctor C 0).obj Z) (CochainComplex.mappingCone S.f) q :=
  CochainComplex.mappingCone.liftCocycle S.f (-representativeCocycle S s q f hf)
    (middleCochain S s q f) rfl (middleCochain_cone_relation S s q f hf)

end HomologicalComplex.SplitBoundary

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace HomologicalComplex.SplitBoundary
open CochainComplex.HomComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/--
Let C be an abelian category and S=(A→B→D) a short complex of integer cochain complexes, split
degreewise with maps r_q:B^q→A^q and s_q:D^q→B^q. Fix an object Z, q∈ℤ and f:Z→D^q. Put
u_q=f≫s_q and ρ_q=u_q≫d_B^q≫r_{q+1}. For closed f, postcomposing the cone cocycle (−ρ_q,u_q)
with the canonical map Cone(S.f)→D recovers the original degree-q cocycle represented by f.
-/
theorem originalConeCocycle_desc (S : ShortComplex (CochainComplex C ℤ))
    (s : ∀ i : ℤ, (S.map (eval C (.up ℤ) i)).Splitting)
    {Z : C} (q : ℤ) (f : Z ⟶ S.X₃.X q) (hf : f ≫ S.X₃.d q (q + 1) = 0) :
    (originalConeCocycle S s q f hf).postcomp
        (CochainComplex.mappingCone.descShortComplex S) =
      Cocycle.fromSingleMk f (zero_add q) (q + 1) rfl hf := by
  apply Cocycle.ext
  change (CochainComplex.mappingCone.liftCochain S.f
      (-representativeCocycle S s q f hf).val (middleCochain S s q f) rfl).comp
      (Cochain.ofHom (CochainComplex.mappingCone.descShortComplex S)) (add_zero _) =
    Cochain.fromSingleMk f (zero_add q)
  rw [CochainComplex.mappingCone.descShortComplex, CochainComplex.mappingCone.ofHom_desc,
    CochainComplex.mappingCone.liftCochain_descCochain, Cochain.comp_zero, zero_add]
  change (Cochain.fromSingleMk (cycleLift S s q f) (zero_add q)).comp
      (Cochain.ofHom S.g) (add_zero _) = Cochain.fromSingleMk f (zero_add q)
  rw [← Cochain.fromSingleMk_postcomp, cycleLift_project]

end HomologicalComplex.SplitBoundary

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace HomologicalComplex.SplitBoundary
open CochainComplex.HomComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/--
Let C be an abelian category and S=(A→B→D) a short complex of integer cochain complexes, split
degreewise with maps r_q:B^q→A^q and s_q:D^q→B^q. Fix an object Z, q∈ℤ and f:Z→D^q. Put
u_q=f≫s_q and ρ_q=u_q≫d_B^q≫r_{q+1}. For closed f, postcomposing (−ρ_q,u_q) with the third
cone-triangle arrow Cone(S.f)→A⟦1⟧ and removing the shift gives the positive connecting
cocycle ρ_q in A^{q+1}.
-/
theorem originalConeCocycle_boundary (S : ShortComplex (CochainComplex C ℤ))
    (s : ∀ i : ℤ, (S.map (eval C (.up ℤ) i)).Splitting)
    {Z : C} (q : ℤ) (f : Z ⟶ S.X₃.X q) (hf : f ≫ S.X₃.d q (q + 1) = 0) :
    ((originalConeCocycle S s q f hf).postcomp
        (CochainComplex.mappingCone.triangle S.f).mor₃).rightUnshift (q + 1) rfl =
      representativeCocycle S s q f hf := by
  have h : (CochainComplex.mappingCone.triangle S.f).mor₃ =
      Cocycle.equivHomShift.symm (-CochainComplex.mappingCone.fst S.f) := rfl
  rw [h]
  have hp := Cocycle.postcomp_equivHomShift_rightUnshift
    (originalConeCocycle S s q f hf) (-CochainComplex.mappingCone.fst S.f)
  apply Cocycle.ext
  refine hp.trans ?_
  change (CochainComplex.mappingCone.liftCochain S.f
      (-representativeCocycle S s q f hf).val (middleCochain S s q f) rfl).comp
      (-(CochainComplex.mappingCone.fst S.f).val) rfl =
    (representativeCocycle S s q f hf).val
  rw [Cochain.comp_neg, CochainComplex.mappingCone.liftCochain_fst]
  exact neg_neg _

end HomologicalComplex.SplitBoundary

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
universe u v
namespace HomologicalComplex.SplitBoundary
open CochainComplex.HomComplex
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

set_option backward.isDefEq.respectTransparency false in
/--
Let C be an abelian category and S=(A→B→D) a short complex of integer cochain complexes, split
degreewise with r_q:B^q→A^q and s_q:D^q→B^q. Fix Z, q∈ℤ and f:Z→D^q. Put u_q=f≫s_q and
ρ_q=u_q≫d_B^q≫r_{q+1}. Assume C has a derived category, S is short exact and f is closed. Let
Z[0] be the complex concentrated at Z in degree zero and Q the canonical derived-category
functor. In the long exact Hom(Q(Z[0]),−) sequence of the derived short-exact triangle, the
connecting map sends the shifted class of f to the shifted class of ρ_q.
-/
theorem derived_SES_original_cocycle_boundary
    (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
    (s : ∀ i : ℤ, (S.map (eval C (.up ℤ) i)).Splitting)
    {Z : C} (q : ℤ) (f : Z ⟶ S.X₃.X q) (hf : f ≫ S.X₃.d q (q + 1) = 0) :
    (preadditiveCoyoneda.obj (op (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor C 0).obj Z)))).homologySequenceδ
      (DerivedCategory.triangleOfSES hS) q (q + 1) rfl
      (Cocycle.mappedShiftedHom DerivedCategory.Q
        (Cocycle.fromSingleMk f (zero_add q) (q + 1) rfl hf)) =
    Cocycle.mappedShiftedHom DerivedCategory.Q (representativeCocycle S s q f hf) := by
  let z := originalConeCocycle S s q f hf
  have hp := Cocycle.mappedShiftedHom_postcomp DerivedCategory.Q z
    (CochainComplex.mappingCone.descShortComplex S)
  rw [originalConeCocycle_desc] at hp
  have hb := Cocycle.mappedShiftedHom_boundary DerivedCategory.Q
    (CochainComplex.mappingCone.triangle S.f) q z
  rw [originalConeCocycle_boundary] at hb
  have : IsIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S)) := by
    have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
    infer_instance
  rw [Pretriangulated.preadditiveCoyoneda_homologySequenceδ_apply]
  rw [hp]
  dsimp only [DerivedCategory.triangleOfSES, Triangle.mk_mor₃, DerivedCategory.triangleOfSESδ]
  rw [Functor.map_comp, Functor.map_comp]
  have hc : (shiftFunctor (DerivedCategory C) q).map
      (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S)) ≫
      (shiftFunctor (DerivedCategory C) q).map
        (CategoryTheory.inv (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S))) =
      𝟙 _ := by
    rw [← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
  dsimp only [CochainComplex.mappingCone.triangle] at hb ⊢
  simp only [Category.assoc]
  rw [reassoc_of% hc]
  dsimp only [Triangle.mk_obj₁]
  have hb' := hb
  rw [Pretriangulated.preadditiveCoyoneda_homologySequenceδ_apply] at hb'
  dsimp only [CategoryTheory.Functor.mapTriangle, Triangle.mk_obj₁, Triangle.mk_mor₃] at hb'
  dsimp only [Triangle.mk_mor₃] at hb' ⊢
  simpa only [Functor.map_comp, Category.assoc] using hb'

end HomologicalComplex.SplitBoundary

end
