/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.KanComplex.HomotopyGroup
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SphereFaceCorrection
public import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexContraction

/-!
# Sphere fillers in nonempty Kan complexes with trivial homotopy

Let F be a Kan complex with a chosen vertex x₀, and suppose every based homotopy set πₙ(F,x) is
subsingleton for every n∈ℕ and every vertex x. Every boundary sphere s:∂Δ[n]→F then extends over
Δ[n]. For n=0, the chosen vertex supplies the extension.

The construction uses lower-dimensional boundary fillings, standard-simplex contractions, Kan
horn fillings and relative face corrections. The two cap orientations are explicit: the face and
boundary homotopies extend from cap zero, and the final filler transports back through a cap-one
cylinder. All simplicial sets are in an arbitrary universe u.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Simplicial SSet
  Opposite
open scoped Simplicial

namespace SSet.KanComplex

variable {F : SSet.{u}} [KanComplex F]

omit [KanComplex F] in
private theorem filler_zero (x₀ : F _⦋0⦌) (s : (∂Δ[0] : SSet.{u}) ⟶ F) :
    ∃ _t : Δ[0] ⟶ F, (SSet.boundary 0).ι ≫ _t = s :=
  ⟨SSet.const x₀, SSet.boundary.hom_ext₀⟩

/-- For n∈ℕ, the capped cylinder Cₙ⊆Δ[n]×Δ[1] is (∂Δ[n]×Δ[1])∪(Δ[n]×{1}). -/
private noncomputable def capSubcomplex (n : ℕ) :
    (Δ[n] ⊗ (Δ[1] : SSet.{u})).Subcomplex :=
  (SSet.boundary n).unionProd
    (SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex)

/-- For every n∈ℕ, the inclusion (∂Δ[n]×Δ[1])∪(Δ[n]×{1})→Δ[n]×Δ[1] is anodyne. -/
private theorem cap_mem_anodyneExtensions (n : ℕ) :
    SSet.anodyneExtensions.{u} (capSubcomplex (n := n)).ι := by
  have h_face : SSet.anodyneExtensions.{u}
      (SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).ι := by
    have h_eq : (SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex) =
        SSet.horn (n := 1) (1 : Fin 2) := by
      have h_fin : ({1} : Finset (Fin 2)) = {0}ᶜ := by decide
      calc (SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex)
          = SSet.stdSimplex.face ({0}ᶜ : Finset (Fin 2)) := by rw [h_fin]
        _ = SSet.horn (n := 1) (1 : Fin 2) := by
            ext m x
            simp [SSet.horn_eq_iSup]
    rw [h_eq]
    exact SSet.anodyneExtensions.horn_ι (1 : Fin 2)
  have h : SSet.anodyneExtensions.{u}
      ((SSet.boundary n).unionProd
        (SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex)).ι :=
    SSet.anodyneExtensions_unionProd_ι (SSet.boundary n) _ h_face
  simpa [capSubcomplex] using h

/-- For any simplex degree n and horn index i∈Fin(n+1), the horn Λⁱ[n] is a subcomplex of ∂Δ[n]. -/
private theorem horn_le_boundary {n : ℕ} (i : Fin (n + 1)) :
    SSet.horn n i ≤ SSet.boundary n := by
  rw [SSet.horn_eq_iSup]
  refine iSup_le fun j ↦ ?_
  exact SSet.face_singleton_compl_le_boundary j.1

/-- Let F be a Kan complex. For s:∂Δ[n+1]→F and i∈Fin(n+2), choose a Kan filler of the restriction
of s to Λⁱ[n+1]. -/
private noncomputable def hornFill {n : ℕ} (i : Fin (n + 2))
    (s : (∂Δ[n + 1] : SSet.{u}) ⟶ F) : Δ[n + 1] ⟶ F :=
  (SSet.KanComplex.hornFilling
    (Subcomplex.homOfLE (horn_le_boundary i) ≫ s)).choose

/-- Let F be a Kan complex. The chosen filler of s restricted to Λⁱ[n+1] agrees with s on that horn. -/
private theorem hornFill_spec {n : ℕ} (i : Fin (n + 2))
    (s : (∂Δ[n + 1] : SSet.{u}) ⟶ F) :
    Subcomplex.homOfLE (horn_le_boundary i) ≫ s =
      (SSet.horn (n + 1) i).ι ≫ hornFill i s :=
  (SSet.KanComplex.hornFilling _).choose_spec

/-!
## Boundary homotopy and face correction

For a sphere in dimension m+1, fill the ridge of its selected face in dimension m. Contracting
this filler makes the face boundary constant. A cap-zero extension changes the selected face,
and another extends that change across the boundary.

A horn filler of the modified boundary has the same constant ridge on its missing face.
Subsingleton based homotopy identifies that face with the prescribed one, permitting a relative
face correction. The corrected simplex fills the modified sphere; a cap-one extension then gives
a filler of the original sphere at endpoint zero.
-/

/-- For m∈ℕ and k∈Fin(m+2), the k-th face map Δ[m]→Δ[m+1] factors canonically through ∂Δ[m+1]. -/
private noncomputable def faceInclBd (m : ℕ) (k : Fin (m + 2)) :
    (Δ[m] : SSet.{u}) ⟶ (∂Δ[m + 1] : SSet.{u}) :=
  (SSet.stdSimplex.faceSingletonComplIso k).hom ≫
    Subcomplex.homOfLE (SSet.face_singleton_compl_le_boundary k)

/-- The canonical k-th face inclusion Δ[m]→∂Δ[m+1], followed by the boundary inclusion, is
δₖ:Δ[m]→Δ[m+1]. -/
private theorem faceInclBd_ι (m : ℕ) (k : Fin (m + 2)) :
    faceInclBd m k ≫ (SSet.boundary (m + 1)).ι = SSet.stdSimplex.δ k := by
  rw [faceInclBd, Category.assoc, Subcomplex.homOfLE_ι,
    SSet.stdSimplex.faceSingletonComplIso_hom_ι]

/-- For m∈ℕ and k∈Fin(m+2), the image of ∂Δ[m] under δₖ lies in the complementary horn Λᵏ[m+1]. -/
private theorem ridge_le_horn (m : ℕ) (k : Fin (m + 2)) :
    Subcomplex.range ((SSet.boundary m).ι ≫ SSet.stdSimplex.δ k) ≤
      SSet.horn (m + 1) k := by
  intro n x hx
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = Opposite.op ⦋d⦌ := ⟨n.unop.len, rfl⟩
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨zval, hz⟩ := z
  obtain ⟨j', hj'⟩ := (SSet.mem_boundary_iff_notMem_range _).mp hz
  refine (SSet.mem_horn_iff_notMem_range _ _).mpr
    ⟨k.succAbove j', Fin.succAbove_ne _ _, ?_⟩
  rintro ⟨a, ha⟩
  apply hj'
  refine ⟨a, ?_⟩
  have hδ : (SSet.stdSimplex.δ k).app _ zval a = k.succAbove (zval a) := rfl
  have hxa : (SSet.stdSimplex.δ k).app _ zval a = k.succAbove j' := ha
  rw [hδ] at hxa
  exact Fin.succAbove_right_injective hxa

/-- For m∈ℕ and k∈Fin(m+2), the boundary of the k-th face has its canonical map ∂Δ[m]→Λᵏ[m+1]. -/
private noncomputable def ridgeToHorn (m : ℕ) (k : Fin (m + 2)) :
    (∂Δ[m] : SSet.{u}) ⟶ (SSet.horn (m + 1) k : SSet.{u}) :=
  Subcomplex.lift _ (ridge_le_horn m k)

/-- The ridge map ∂Δ[m]→Λᵏ[m+1] followed by horn inclusion equals the boundary inclusion ∂Δ[m]→Δ[m]
followed by δₖ. -/
private theorem ridgeToHorn_spec (m : ℕ) (k : Fin (m + 2)) :
    ridgeToHorn m k ≫ (SSet.horn (m + 1) k).ι =
      (SSet.boundary m).ι ≫ SSet.stdSimplex.δ k :=
  Subcomplex.lift_ι _ _

/-- For c:Δ[m]→F, the last-vertex contraction of Δ[m] restricts to a homotopy on ∂Δ[m] from its
c-boundary to the constant last-vertex value c(v_last). -/
private noncomputable def ridgeNullMap (m : ℕ) (c : (Δ[m] : SSet.{u}) ⟶ F) :
    (∂Δ[m] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ F :=
  ((SSet.boundary m).ι ▷ (Δ[1] : SSet.{u})) ≫
    (SSet.stdSimplex.homotopyIdConstLast m).h ≫ c

omit [KanComplex F] in
/-- For c:Δ[m]→F, the endpoint-zero restriction of its ridge null-homotopy is the boundary
restriction of c. -/
private theorem ridgeNullMap_h₀ (m : ℕ) (c : (Δ[m] : SSet.{u}) ⟶ F) :
    SSet.ι₀ ≫ ridgeNullMap m c = (SSet.boundary m).ι ≫ c := by
  have e : SSet.ι₀ ≫ ((SSet.boundary m).ι ▷ (Δ[1] : SSet.{u})) =
      (SSet.boundary m).ι ≫ SSet.ι₀ :=
    SSet.ι₀_comp _
  have h0 : SSet.ι₀ ≫
      ((SSet.stdSimplex.homotopyIdConstLast m).h ≫ c) =
      𝟙 _ ≫ c := by
    rw [← Category.assoc, (SSet.stdSimplex.homotopyIdConstLast m).h₀]
  calc SSet.ι₀ ≫ ridgeNullMap m c
      = (SSet.boundary m).ι ≫ (SSet.ι₀ ≫
          ((SSet.stdSimplex.homotopyIdConstLast m).h ≫ c)) := by
        rw [ridgeNullMap, ← Category.assoc, ← Category.assoc, e, Category.assoc,
          Category.assoc]
    _ = (SSet.boundary m).ι ≫ c := by rw [h0, Category.id_comp]

omit [KanComplex F] in
/-- For c:Δ[m]→F, the endpoint-one restriction of its ridge null-homotopy is constant at c(v_last). -/
private theorem ridgeNullMap_h₁ (m : ℕ) (c : (Δ[m] : SSet.{u}) ⟶ F) :
    SSet.ι₁ ≫ ridgeNullMap m c =
      SSet.const (c.app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last m))) := by
  have e : SSet.ι₁ ≫ ((SSet.boundary m).ι ▷ (Δ[1] : SSet.{u})) =
      (SSet.boundary m).ι ≫ SSet.ι₁ :=
    SSet.ι₁_comp _
  have h1 : SSet.ι₁ ≫
      ((SSet.stdSimplex.homotopyIdConstLast m).h ≫ c) =
      SSet.const (c.app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last m))) := by
    rw [← Category.assoc, (SSet.stdSimplex.homotopyIdConstLast m).h₁]
    exact SSet.const_comp _ _
  calc SSet.ι₁ ≫ ridgeNullMap m c
      = (SSet.boundary m).ι ≫ (SSet.ι₁ ≫
          ((SSet.stdSimplex.homotopyIdConstLast m).h ≫ c)) := by
        rw [ridgeNullMap, ← Category.assoc, ← Category.assoc, e, Category.assoc,
          Category.assoc]
    _ = SSet.const (c.app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last m))) := by
        rw [h1]
        exact SSet.comp_const _ _

/-- The vertex-zero inclusion {0}→Δ[1], equivalently the horn Λ⁰[1]→Δ[1], is anodyne. -/
private theorem faceZero_mem_anodyne :
    SSet.anodyneExtensions.{u}
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι := by
  have h_eq : (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) =
      SSet.horn (n := 1) (0 : Fin 2) := by
    have h_fin : ({0} : Finset (Fin 2)) = {1}ᶜ := by decide
    calc (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)
        = SSet.stdSimplex.face ({1}ᶜ : Finset (Fin 2)) := by rw [h_fin]
      _ = SSet.horn (n := 1) (0 : Fin 2) := by
          ext m x
          simp [SSet.horn_eq_iSup]
  rw [h_eq]
  exact SSet.anodyneExtensions.horn_ι (0 : Fin 2)

omit [KanComplex F] in
/-- For maps fₖ,c:Δ[m]→F agreeing on ∂Δ[m], the constant face map on Δ[m]×{0} and the ridge
null-homotopy on ∂Δ[m]×Δ[1] agree on their intersection ∂Δ[m]×{0}. -/
private theorem agree1 (m : ℕ) (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk) :
    ((SSet.boundary m).ι ▷
        ((SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u})) ≫
      (fst _ _ ≫ fk) =
      (((SSet.boundary m : SSet.{u}) ◁
          (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι) ≫
        ridgeNullMap m c) := by
  ext n ⟨⟨z, hz⟩, ⟨t, ht⟩⟩
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = Opposite.op ⦋d⦌ := ⟨n.unop.len, rfl⟩
  have ht0 : ∀ a, t a = (0 : Fin 2) := fun a =>
    Finset.mem_singleton.mp ((SSet.stdSimplex.mem_face_iff _ _).mp ht a)
  have hpair : (⟨⟨z, hz⟩, ((SSet.stdSimplex.face {0} :
      (Δ[1] : SSet.{u}).Subcomplex).ι.app _ ⟨t, ht⟩)⟩ :
      ((((SSet.boundary m : SSet.{u}) ⊗ (Δ[1] : SSet.{u})).obj
        (Opposite.op ⦋d⦌)))) =
      SSet.ι₀.app _ (⟨z, hz⟩ : ((SSet.boundary m : SSet.{u}).obj
        (Opposite.op ⦋d⦌))) := by
    refine Prod.ext rfl ?_
    dsimp only
    change t = _
    ext a
    simp only [ht0]
    congr 1
  have hH0 : (ridgeNullMap m c).app _ ⟨⟨z, hz⟩,
      ((SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι.app _
        ⟨t, ht⟩)⟩ =
      ((SSet.boundary m).ι ≫ fk).app _ ⟨z, hz⟩ := by
    calc (ridgeNullMap m c).app _ ⟨⟨z, hz⟩,
          ((SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι.app _
            ⟨t, ht⟩)⟩
        = (ridgeNullMap m c).app _ (SSet.ι₀.app _ ⟨z, hz⟩) := by rw [← hpair]
      _ = (SSet.ι₀ ≫ ridgeNullMap m c).app _ ⟨z, hz⟩ := rfl
      _ = ((SSet.boundary m).ι ≫ c).app _ ⟨z, hz⟩ := by rw [ridgeNullMap_h₀]
      _ = ((SSet.boundary m).ι ≫ fk).app _ ⟨z, hz⟩ := by rw [hbc]
  have hgoal : ((((SSet.boundary m).ι ▷
      ((SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u})) ≫
      (fst _ _ ≫ fk)).app _ ⟨⟨z, hz⟩, ⟨t, ht⟩⟩) =
      ((((SSet.boundary m : SSet.{u}) ◁
        (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι) ≫
        ridgeNullMap m c).app _ ⟨⟨z, hz⟩, ⟨t, ht⟩⟩) := by
    calc ((((SSet.boundary m).ι ▷
        ((SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u})) ≫
        (fst _ _ ≫ fk)).app _ ⟨⟨z, hz⟩, ⟨t, ht⟩⟩)
        = fk.app _ z := rfl
      _ = ((SSet.boundary m).ι ≫ fk).app _ ⟨z, hz⟩ := rfl
      _ = (ridgeNullMap m c).app _ ⟨⟨z, hz⟩,
          ((SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι.app _
            ⟨t, ht⟩)⟩ := hH0.symm
      _ = _ := rfl
  exact hgoal

omit [KanComplex F] in
/-- Let S⊆X, f:X→F and g a map on (S×Δ[1])∪(X×{0}) whose cap-zero restriction is f. Any extension
Φ:X×Δ[1]→F of g has endpoint-zero restriction f. -/
private theorem iota_zero_of_lift {X : SSet.{u}} (S : X.Subcomplex) (f : X ⟶ F)
    (Φ : X ⊗ (Δ[1] : SSet.{u}) ⟶ F)
    (gR : ((S.unionProd
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)) : SSet.{u}) ⟶ F)
    (hgR1 : Subcomplex.unionProd.ι₁ S (SSet.stdSimplex.face {0}) ≫ gR =
      fst _ _ ≫ f)
    (hΦlift : (S.unionProd (SSet.stdSimplex.face {0})).ι ≫ Φ = gR) :
    SSet.ι₀ ≫ Φ = f := by
  ext n x
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = Opposite.op ⦋d⦌ := ⟨n.unop.len, rfl⟩
  have hmem2 : (SSet.ι₀.app (Opposite.op ⦋d⦌) x).2 ∈
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).obj
        (Opposite.op ⦋d⦌) := by
    rw [SSet.stdSimplex.mem_face_iff]
    intro i
    exact Finset.mem_singleton.mpr (SSet.ι₀_app_snd_apply x i)
  have hmem : SSet.ι₀.app (Opposite.op ⦋d⦌) x ∈
      (S.unionProd (SSet.stdSimplex.face {0})).obj (Opposite.op ⦋d⦌) :=
    Or.inl ⟨Set.mem_univ _, hmem2⟩
  have e1 : Φ.app _ (SSet.ι₀.app _ x) =
      gR.app _ ⟨SSet.ι₀.app _ x, hmem⟩ := by
    have h := congrArg (fun ψ :
        ((S.unionProd (SSet.stdSimplex.face {0})) : SSet.{u}) ⟶ F =>
        ψ.app _ ⟨SSet.ι₀.app _ x, hmem⟩) hΦlift
    exact h
  have e2 : (⟨SSet.ι₀.app _ x, hmem⟩ :
      ((S.unionProd (SSet.stdSimplex.face {0})) : SSet.{u}).obj _) =
      (Subcomplex.unionProd.ι₁ S (SSet.stdSimplex.face {0})).app _ ⟨x,
        ⟨(SSet.ι₀.app _ x).2, hmem2⟩⟩ := by
    apply Subtype.ext
    change SSet.ι₀.app _ x = _
    rfl
  have e3 : gR.app _ ⟨SSet.ι₀.app _ x, hmem⟩ = f.app _ x := by
    calc gR.app _ ⟨SSet.ι₀.app _ x, hmem⟩
        = gR.app _ ((Subcomplex.unionProd.ι₁ S
            (SSet.stdSimplex.face {0})).app _ ⟨x,
              ⟨(SSet.ι₀.app _ x).2, hmem2⟩⟩) := by rw [← e2]
      _ = (Subcomplex.unionProd.ι₁ S (SSet.stdSimplex.face {0}) ≫ gR).app _
          ⟨x, ⟨(SSet.ι₀.app _ x).2, hmem2⟩⟩ := rfl
      _ = (fst X ((SSet.stdSimplex.face {0} :
            (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ≫ f).app _
          ⟨x, ⟨(SSet.ι₀.app _ x).2, hmem2⟩⟩ := by rw [hgR1]
      _ = f.app _ x := rfl
  calc (SSet.ι₀ ≫ Φ).app _ x = Φ.app _ (SSet.ι₀.app _ x) := rfl
    _ = gR.app _ ⟨SSet.ι₀.app _ x, hmem⟩ := e1
    _ = f.app _ x := e3

omit [KanComplex F] in
/-- For fₖ,c:Δ[m]→F with the same boundary, glue the constant fₖ map on Δ[m]×{0} to c's ridge
null-homotopy on ∂Δ[m]×Δ[1]. This defines the map on the cap-zero union. -/
private noncomputable def gR1 (m : ℕ) (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk) :
    (((SSet.boundary m).unionProd
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)) : SSet.{u}) ⟶ F :=
  (Subcomplex.unionProd.isPushout (SSet.boundary m)
    (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)).desc
    (fst _ _ ≫ fk) (ridgeNullMap m c) (agree1 m fk c hbc)

omit [KanComplex F] in
/-- For every m∈ℕ, the cap-zero inclusion (∂Δ[m]×Δ[1])∪(Δ[m]×{0})→Δ[m]×Δ[1] is anodyne. -/
private theorem cap1_mem_anodyne (m : ℕ) :
    SSet.anodyneExtensions (((SSet.boundary m).unionProd
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)).ι) :=
  SSet.anodyneExtensions_unionProd_ι _ _ faceZero_mem_anodyne

/-- Let F be a Kan complex. For m∈ℕ and maps fₖ,c:Δ[m]→F with the same boundary restriction, let H₁
be the cap-zero extension of the constant face fₖ and the boundary null-homotopy induced by c.
This gives the chosen extension H₁:Δ[m]×Δ[1]→F of the two compatible partial maps. -/
private noncomputable def lift1 (m : ℕ) (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk) :
    (Δ[m] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ F :=
  (SSet.anodyneExtensions.exists_lift_of_isFibrant (gR1 m fk c hbc)
    (cap1_mem_anodyne m)).choose

private theorem lift1_spec (m : ℕ) (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk) :
    (((SSet.boundary m).unionProd
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)).ι ≫
      lift1 m fk c hbc) = gR1 m fk c hbc :=
  (SSet.anodyneExtensions.exists_lift_of_isFibrant (gR1 m fk c hbc)
    (cap1_mem_anodyne m)).choose_spec

/-- Let F be a Kan complex. For m∈ℕ and maps fₖ,c:Δ[m]→F with the same boundary restriction, let H₁
be the cap-zero extension of the constant face fₖ and the boundary null-homotopy induced by c.
The endpoint-zero restriction of H₁ is fₖ. -/
private theorem lift1_zero (m : ℕ) (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk) :
    SSet.ι₀ ≫ lift1 m fk c hbc = fk := by
  have hg := (Subcomplex.unionProd.isPushout (SSet.boundary m)
    (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)).inl_desc
    (fst _ _ ≫ fk) (ridgeNullMap m c) (agree1 m fk c hbc)
  exact iota_zero_of_lift _ _ _ _ hg (lift1_spec m fk c hbc)

/-- Let F be a Kan complex. For m∈ℕ and maps fₖ,c:Δ[m]→F with the same boundary restriction, let H₁
be the cap-zero extension of the constant face fₖ and the boundary null-homotopy induced by c.
The modified face f′ₖ:Δ[m]→F is the endpoint-one restriction of H₁. -/
private noncomputable def fk' (m : ℕ) (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk) :
    (Δ[m] : SSet.{u}) ⟶ F :=
  SSet.ι₁ ≫ lift1 m fk c hbc

/-- Let F be a Kan complex. For m∈ℕ and maps fₖ,c:Δ[m]→F with the same boundary restriction, let H₁
be the cap-zero extension of the constant face fₖ and the boundary null-homotopy induced by c.
The modified face f′ₖ has constant boundary at c(v_last). -/
private theorem fk'_ridge (m : ℕ) (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk) :
    (SSet.boundary m).ι ≫ fk' m fk c hbc =
      SSet.const (c.app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last m))) := by
  have hside : ((SSet.boundary m).ι ▷ (Δ[1] : SSet.{u})) ≫ lift1 m fk c hbc =
      ridgeNullMap m c := by
    rw [← Subcomplex.unionProd.ι₂_ι (SSet.boundary m)
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex),
      Category.assoc, lift1_spec m fk c hbc]
    exact (Subcomplex.unionProd.isPushout _ _).inr_desc _ _ _
  calc (SSet.boundary m).ι ≫ fk' m fk c hbc
      = (SSet.boundary m).ι ≫ (SSet.ι₁ ≫ lift1 m fk c hbc) := rfl
    _ = SSet.ι₁ ≫ (((SSet.boundary m).ι ▷ (Δ[1] : SSet.{u})) ≫
          lift1 m fk c hbc) := by
        rw [← Category.assoc, ← Category.assoc, SSet.ι₁_comp]
    _ = SSet.const (c.app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last m))) := by
        rw [hside, ridgeNullMap_h₁]

omit [KanComplex F] in
/-- For m∈ℕ and k∈Fin(m+2), take the subcomplex of ∂Δ[m+1] consisting of its k-th face, equivalently
the preimage of that face under the boundary inclusion. -/
private noncomputable def faceSubBd (m : ℕ) (k : Fin (m + 2)) :
    (∂Δ[m + 1] : SSet.{u}).Subcomplex :=
  Subcomplex.preimage (SSet.stdSimplex.face {k}ᶜ)
    (SSet.boundary (m + 1)).ι

omit [KanComplex F] in
private theorem faceSubBd_range_le (m : ℕ) (k : Fin (m + 2)) :
    Subcomplex.range (faceInclBd m k) ≤ faceSubBd m k := by
  intro N y hy
  obtain ⟨z, rfl⟩ := hy
  change (SSet.boundary (m + 1)).ι.app N ((faceInclBd m k).app N z) ∈
    (SSet.stdSimplex.face {k}ᶜ).obj N
  have e : (SSet.boundary (m + 1)).ι.app N ((faceInclBd m k).app N z) =
      (SSet.stdSimplex.δ k).app N z := by
    calc (SSet.boundary (m + 1)).ι.app N ((faceInclBd m k).app N z)
        = ((faceInclBd m k ≫ (SSet.boundary (m + 1)).ι).app N z) := rfl
      _ = ((SSet.stdSimplex.δ k).app N z) := by rw [faceInclBd_ι m k]
  rw [e, ← SSet.stdSimplex.range_δ]
  exact ⟨z, rfl⟩

omit [KanComplex F] in
/-- The k-th face parametrization Δ[m]→∂Δ[m+1] lifts to its face subcomplex Aₖ. -/
private noncomputable def faceSubBdHom (m : ℕ) (k : Fin (m + 2)) :
    (Δ[m] : SSet.{u}) ⟶ ((faceSubBd m k : SSet.{u})) :=
  Subcomplex.lift (faceInclBd m k) (faceSubBd_range_le m k)

omit [KanComplex F] in
/-- The face subcomplex Aₖ of ∂Δ[m+1] has its inverse coordinate map Aₖ→Δ[m]. -/
private noncomputable def faceSubBdInv (m : ℕ) (k : Fin (m + 2)) :
    ((faceSubBd m k : SSet.{u})) ⟶ (Δ[m] : SSet.{u}) :=
  Subcomplex.fromPreimage (SSet.stdSimplex.face {k}ᶜ)
    (SSet.boundary (m + 1)).ι ≫
    (SSet.stdSimplex.faceSingletonComplIso k).inv

omit [KanComplex F] in
/-- The parametrization Δ[m]→Aₖ followed by the inverse coordinate map Aₖ→Δ[m] is the identity of
Δ[m]. -/
private theorem faceSubBd_hom_inv (m : ℕ) (k : Fin (m + 2)) :
    faceSubBdHom m k ≫ faceSubBdInv m k = 𝟙 _ := by
  have hH : faceSubBdHom m k ≫ (faceSubBd m k).ι = faceInclBd m k := rfl
  have hFP : Subcomplex.fromPreimage (SSet.stdSimplex.face {k}ᶜ)
        (SSet.boundary (m + 1)).ι ≫ (SSet.stdSimplex.face {k}ᶜ).ι =
      (faceSubBd m k).ι ≫ (SSet.boundary (m + 1)).ι := rfl
  have hface : faceSubBdHom m k ≫
      Subcomplex.fromPreimage (SSet.stdSimplex.face {k}ᶜ)
        (SSet.boundary (m + 1)).ι =
      (SSet.stdSimplex.faceSingletonComplIso k).hom := by
    apply (cancel_mono (SSet.stdSimplex.face {k}ᶜ).ι).mp
    calc (faceSubBdHom m k ≫
              Subcomplex.fromPreimage (SSet.stdSimplex.face {k}ᶜ)
                (SSet.boundary (m + 1)).ι) ≫
            (SSet.stdSimplex.face {k}ᶜ).ι
        = faceSubBdHom m k ≫
            (Subcomplex.fromPreimage (SSet.stdSimplex.face {k}ᶜ)
                (SSet.boundary (m + 1)).ι ≫
              (SSet.stdSimplex.face {k}ᶜ).ι) :=
          Category.assoc _ _ _
      _ = faceSubBdHom m k ≫
            ((faceSubBd m k).ι ≫ (SSet.boundary (m + 1)).ι) :=
          congrArg (faceSubBdHom m k ≫ ·) hFP
      _ = (faceSubBdHom m k ≫ (faceSubBd m k).ι) ≫
            (SSet.boundary (m + 1)).ι :=
          (Category.assoc _ _ _).symm
      _ = faceInclBd m k ≫ (SSet.boundary (m + 1)).ι :=
          congrArg (· ≫ (SSet.boundary (m + 1)).ι) hH
      _ = SSet.stdSimplex.δ k := faceInclBd_ι m k
      _ = (SSet.stdSimplex.faceSingletonComplIso k).hom ≫
            (SSet.stdSimplex.face {k}ᶜ).ι :=
          (SSet.stdSimplex.faceSingletonComplIso_hom_ι _).symm
  calc faceSubBdHom m k ≫ faceSubBdInv m k
      = faceSubBdHom m k ≫ (Subcomplex.fromPreimage
            (SSet.stdSimplex.face {k}ᶜ) (SSet.boundary (m + 1)).ι ≫
          (SSet.stdSimplex.faceSingletonComplIso k).inv) := rfl
    _ = (faceSubBdHom m k ≫ Subcomplex.fromPreimage
            (SSet.stdSimplex.face {k}ᶜ) (SSet.boundary (m + 1)).ι) ≫
          (SSet.stdSimplex.faceSingletonComplIso k).inv :=
        (Category.assoc _ _ _).symm
    _ = (SSet.stdSimplex.faceSingletonComplIso k).hom ≫
          (SSet.stdSimplex.faceSingletonComplIso k).inv :=
        congrArg (· ≫ (SSet.stdSimplex.faceSingletonComplIso k).inv) hface
    _ = 𝟙 _ := Iso.hom_inv_id _

omit [KanComplex F] in
/-- In any simplicial degree d, a pair (y,t)∈X_d×Δ[1]_d with t in the vertex-zero face equals the
endpoint-zero image ι₀(y). -/
private theorem iota_zero_pair {X : SSet.{u}} {d : ℕ}
    (y : X.obj (Opposite.op ⦋d⦌))
    (t : (Δ[1] : SSet.{u}).obj (Opposite.op ⦋d⦌))
    (ht : t ∈ (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).obj
      (Opposite.op ⦋d⦌)) :
    (⟨y, (((SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι.app
        (Opposite.op ⦋d⦌)) ⟨t, ht⟩)⟩ :
      (X ⊗ (Δ[1] : SSet.{u})).obj (Opposite.op ⦋d⦌)) =
      SSet.ι₀.app (Opposite.op ⦋d⦌) y := by
  refine Prod.ext rfl ?_
  dsimp only
  change t = _
  ext a
  have ht0 : ∀ a, t a = (0 : Fin 2) := fun a =>
    Finset.mem_singleton.mp ((SSet.stdSimplex.mem_face_iff _ _).mp ht a)
  simp only [ht0]
  congr 1

omit [KanComplex F] in
/-- For a simplex x of the k-th face subcomplex Aₖ, its inverse coordinate followed by the face
parametrization into ∂Δ[m+1] equals the subcomplex inclusion of x. -/
private theorem faceInclBd_inv_apply (m : ℕ) (k : Fin (m + 2))
    {d : ℕ} (x : ((faceSubBd m k : SSet.{u})).obj (Opposite.op ⦋d⦌)) :
    (faceInclBd m k).app _ ((faceSubBdInv m k).app _ x) =
      (faceSubBd m k).ι.app _ x := by
  obtain ⟨a, ha⟩ := x
  have key : ((SSet.boundary (m + 1)).ι.app _ ((faceInclBd m k).app _
      ((faceSubBdInv m k).app _ ⟨a, ha⟩))) =
      ((SSet.boundary (m + 1)).ι.app _ ((faceSubBd m k).ι.app _ ⟨a, ha⟩)) := by
    calc ((SSet.boundary (m + 1)).ι.app _ ((faceInclBd m k).app _
            ((faceSubBdInv m k).app _ ⟨a, ha⟩)))
        = (((faceInclBd m k ≫ (SSet.boundary (m + 1)).ι).app _)
            ((faceSubBdInv m k).app _ ⟨a, ha⟩)) := rfl
      _ = (((SSet.stdSimplex.δ k).app _)
            ((faceSubBdInv m k).app _ ⟨a, ha⟩)) := by
          rw [faceInclBd_ι m k]
      _ = (((((SSet.stdSimplex.faceSingletonComplIso k).hom ≫
            (SSet.stdSimplex.face {k}ᶜ).ι).app _))
            ((faceSubBdInv m k).app _ ⟨a, ha⟩)) := by
          rw [← SSet.stdSimplex.faceSingletonComplIso_hom_ι]
      _ = ((SSet.stdSimplex.face {k}ᶜ).ι.app _
            (((SSet.stdSimplex.faceSingletonComplIso k).hom).app _
              (((SSet.stdSimplex.faceSingletonComplIso k).inv).app _
                ((Subcomplex.fromPreimage (SSet.stdSimplex.face {k}ᶜ)
                  (SSet.boundary (m + 1)).ι).app _ ⟨a, ha⟩)))) := rfl
      _ = ((SSet.stdSimplex.face {k}ᶜ).ι.app _
            (((((SSet.stdSimplex.faceSingletonComplIso k).inv ≫
              (SSet.stdSimplex.faceSingletonComplIso k).hom).app _))
              ((Subcomplex.fromPreimage (SSet.stdSimplex.face {k}ᶜ)
                (SSet.boundary (m + 1)).ι).app _ ⟨a, ha⟩))) := rfl
      _ = ((SSet.stdSimplex.face {k}ᶜ).ι.app _
            ((Subcomplex.fromPreimage (SSet.stdSimplex.face {k}ᶜ)
              (SSet.boundary (m + 1)).ι).app _ ⟨a, ha⟩)) := by
          rw [Iso.inv_hom_id]
          rfl
      _ = (((Subcomplex.fromPreimage (SSet.stdSimplex.face {k}ᶜ)
              (SSet.boundary (m + 1)).ι ≫
            (SSet.stdSimplex.face {k}ᶜ).ι).app _) ⟨a, ha⟩) := rfl
      _ = ((((Subcomplex.preimage (SSet.stdSimplex.face {k}ᶜ)
              (SSet.boundary (m + 1)).ι).ι ≫
            (SSet.boundary (m + 1)).ι).app _) ⟨a, ha⟩) := by
          rw [Subcomplex.fromPreimage_ι]
      _ = ((SSet.boundary (m + 1)).ι.app _ ((faceSubBd m k).ι.app _ ⟨a, ha⟩)) :=
          rfl
  exact SetCoe.ext key

/-- Let F be a Kan complex. For m∈ℕ and maps fₖ,c:Δ[m]→F with the same boundary restriction, let H₁
be the cap-zero extension of the constant face fₖ and the boundary null-homotopy induced by c.
For a boundary sphere s:∂Δ[m+1]→F with selected k-th face fₖ, let H_B be the boundary homotopy
extending H₁, and s′ its endpoint-one restriction. The constant boundary map s on cap zero and
the transferred face homotopy on Aₖ×Δ[1] agree on Aₖ×{0}. -/
private theorem agree2 (m : ℕ) (k : Fin (m + 2))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    ((faceSubBd m k).ι ▷
        ((SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u})) ≫
      (fst _ _ ≫ s) =
      (((faceSubBd m k : SSet.{u}) ◁
          (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι) ≫
        ((faceSubBdInv m k ▷ (Δ[1] : SSet.{u})) ≫ lift1 m fk c hbc)) := by
  ext N ⟨⟨a, ha⟩, ⟨t, ht⟩⟩
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, N = Opposite.op ⦋d⦌ := ⟨N.unop.len, rfl⟩
  have hpair : (⟨(faceSubBdInv m k).app _ ⟨a, ha⟩,
      (((SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι.app _)
        ⟨t, ht⟩)⟩ :
      (((Δ[m] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})).obj (Opposite.op ⦋d⦌))) =
      SSet.ι₀.app _ ((faceSubBdInv m k).app _ ⟨a, ha⟩) :=
    iota_zero_pair _ _ _
  have hH0 : ((((faceSubBd m k : SSet.{u}) ◁
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι) ≫
      ((faceSubBdInv m k ▷ (Δ[1] : SSet.{u})) ≫ lift1 m fk c hbc)).app _
      ⟨⟨a, ha⟩, ⟨t, ht⟩⟩) =
      fk.app _ ((faceSubBdInv m k).app _ ⟨a, ha⟩) := by
    calc ((((faceSubBd m k : SSet.{u}) ◁
        (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι) ≫
        ((faceSubBdInv m k ▷ (Δ[1] : SSet.{u})) ≫ lift1 m fk c hbc)).app _
        ⟨⟨a, ha⟩, ⟨t, ht⟩⟩)
        = (lift1 m fk c hbc).app _
          (⟨(faceSubBdInv m k).app _ ⟨a, ha⟩,
            (((SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι.app _)
              ⟨t, ht⟩)⟩) := rfl
      _ = (lift1 m fk c hbc).app _
          (SSet.ι₀.app _ ((faceSubBdInv m k).app _ ⟨a, ha⟩)) := by
          rw [hpair]
      _ = (SSet.ι₀ ≫ lift1 m fk c hbc).app _
          ((faceSubBdInv m k).app _ ⟨a, ha⟩) := rfl
      _ = fk.app _ ((faceSubBdInv m k).app _ ⟨a, ha⟩) := by
          rw [lift1_zero m fk c hbc]
  have hgoal : ((((faceSubBd m k).ι ▷
      ((SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u})) ≫
      (fst _ _ ≫ s)).app _ ⟨⟨a, ha⟩, ⟨t, ht⟩⟩) =
      ((((faceSubBd m k : SSet.{u}) ◁
        (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι) ≫
        ((faceSubBdInv m k ▷ (Δ[1] : SSet.{u})) ≫ lift1 m fk c hbc)).app _
        ⟨⟨a, ha⟩, ⟨t, ht⟩⟩) := by
    calc ((((faceSubBd m k).ι ▷
        ((SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) :
          SSet.{u})) ≫
        (fst _ _ ≫ s)).app _ ⟨⟨a, ha⟩, ⟨t, ht⟩⟩)
        = s.app _ a := rfl
      _ = s.app _ ((faceSubBd m k).ι.app _ ⟨a, ha⟩) := rfl
      _ = s.app _ ((faceInclBd m k).app _ ((faceSubBdInv m k).app _ ⟨a, ha⟩)) := by
          rw [faceInclBd_inv_apply m k ⟨a, ha⟩]
      _ = ((faceInclBd m k ≫ s).app _ ((faceSubBdInv m k).app _ ⟨a, ha⟩)) := rfl
      _ = (fk.app _ ((faceSubBdInv m k).app _ ⟨a, ha⟩)) := by rw [← hfk]
      _ = ((((faceSubBd m k : SSet.{u}) ◁
          (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι) ≫
          ((faceSubBdInv m k ▷ (Δ[1] : SSet.{u})) ≫ lift1 m fk c hbc)).app _
          ⟨⟨a, ha⟩, ⟨t, ht⟩⟩) := hH0.symm
  exact hgoal

/-- Let F be a Kan complex. For m∈ℕ and maps fₖ,c:Δ[m]→F with the same boundary restriction, let H₁
be the cap-zero extension of the constant face fₖ and the boundary null-homotopy induced by c.
For a boundary sphere s:∂Δ[m+1]→F with selected k-th face fₖ, let H_B be the boundary homotopy
extending H₁, and s′ its endpoint-one restriction. Glue the constant s map on ∂Δ[m+1]×{0} to the
transferred H₁ map on Aₖ×Δ[1], obtaining the boundary cap-zero map. -/
private noncomputable def gBd1 (m : ℕ) (k : Fin (m + 2))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    ((((faceSubBd m k).unionProd
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)) : SSet.{u})) ⟶ F :=
  (Subcomplex.unionProd.isPushout (faceSubBd m k)
    (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)).desc
    (fst _ _ ≫ s)
    ((faceSubBdInv m k ▷ (Δ[1] : SSet.{u})) ≫ lift1 m fk c hbc)
    (agree2 m k fk c hbc s hfk)

omit [KanComplex F] in
/-- For the k-th face subcomplex Aₖ⊆∂Δ[m+1], the inclusion (Aₖ×Δ[1])∪(∂Δ[m+1]×{0})→∂Δ[m+1]×Δ[1] is
anodyne. -/
private theorem capBd_mem_anodyne (m : ℕ) (k : Fin (m + 2)) :
    SSet.anodyneExtensions (((faceSubBd m k).unionProd
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)).ι) :=
  SSet.anodyneExtensions_unionProd_ι _ _ faceZero_mem_anodyne

/-- Let F be a Kan complex. For m∈ℕ and maps fₖ,c:Δ[m]→F with the same boundary restriction, let H₁
be the cap-zero extension of the constant face fₖ and the boundary null-homotopy induced by c.
For a boundary sphere s:∂Δ[m+1]→F with selected k-th face fₖ, let H_B be the boundary homotopy
extending H₁, and s′ its endpoint-one restriction. The compatible cap-zero map extends to the
boundary homotopy H_B:∂Δ[m+1]×Δ[1]→F. -/
private noncomputable def liftBd (m : ℕ) (k : Fin (m + 2))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    (∂Δ[m + 1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ F :=
  (SSet.anodyneExtensions.exists_lift_of_isFibrant (gBd1 m k fk c hbc s hfk)
    (capBd_mem_anodyne m k)).choose

private theorem liftBd_spec (m : ℕ) (k : Fin (m + 2))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    (((faceSubBd m k).unionProd
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)).ι ≫
      liftBd m k fk c hbc s hfk) = gBd1 m k fk c hbc s hfk :=
  (SSet.anodyneExtensions.exists_lift_of_isFibrant (gBd1 m k fk c hbc s hfk)
    (capBd_mem_anodyne m k)).choose_spec

/-- Let F be a Kan complex. For m∈ℕ and maps fₖ,c:Δ[m]→F with the same boundary restriction, let H₁
be the cap-zero extension of the constant face fₖ and the boundary null-homotopy induced by c.
For a boundary sphere s:∂Δ[m+1]→F with selected k-th face fₖ, let H_B be the boundary homotopy
extending H₁, and s′ its endpoint-one restriction. The endpoint-zero restriction of H_B is the
original boundary sphere s. -/
private theorem liftBd_zero (m : ℕ) (k : Fin (m + 2))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    SSet.ι₀ ≫ liftBd m k fk c hbc s hfk = s := by
  have hg := (Subcomplex.unionProd.isPushout (faceSubBd m k)
    (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)).inl_desc
    (fst _ _ ≫ s)
    ((faceSubBdInv m k ▷ (Δ[1] : SSet.{u})) ≫ lift1 m fk c hbc)
    (agree2 m k fk c hbc s hfk)
  exact iota_zero_of_lift _ _ _ _ hg (liftBd_spec m k fk c hbc s hfk)

/-- Let F be a Kan complex. For m∈ℕ and maps fₖ,c:Δ[m]→F with the same boundary restriction, let H₁
be the cap-zero extension of the constant face fₖ and the boundary null-homotopy induced by c.
For a boundary sphere s:∂Δ[m+1]→F with selected k-th face fₖ, let H_B be the boundary homotopy
extending H₁, and s′ its endpoint-one restriction. The modified boundary s′:∂Δ[m+1]→F is the
endpoint-one restriction of H_B; its k-th face is f′ₖ. -/
private noncomputable def bdFaceFix (m : ℕ) (k : Fin (m + 2))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) : (∂Δ[m + 1] : SSet.{u}) ⟶ F :=
  SSet.ι₁ ≫ liftBd m k fk c hbc s hfk

/-- Let F be a Kan complex. For m∈ℕ and maps fₖ,c:Δ[m]→F with the same boundary restriction, let H₁
be the cap-zero extension of the constant face fₖ and the boundary null-homotopy induced by c.
For a boundary sphere s:∂Δ[m+1]→F with selected k-th face fₖ, let H_B be the boundary homotopy
extending H₁, and s′ its endpoint-one restriction. The k-th face of the modified boundary s′ is
exactly the endpoint-one face f′ₖ of H₁. -/
private theorem face_fix_eq (m : ℕ) (k : Fin (m + 2))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    faceInclBd m k ≫ bdFaceFix m k fk c hbc s hfk = fk' m fk c hbc := by
  have hH : faceSubBdHom m k ≫ (faceSubBd m k).ι = faceInclBd m k := rfl
  have hside : ((faceSubBd m k).ι ▷ (Δ[1] : SSet.{u})) ≫
      liftBd m k fk c hbc s hfk =
      (faceSubBdInv m k ▷ (Δ[1] : SSet.{u})) ≫ lift1 m fk c hbc := by
    rw [← Subcomplex.unionProd.ι₂_ι (faceSubBd m k)
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex),
      Category.assoc, liftBd_spec m k fk c hbc s hfk]
    exact (Subcomplex.unionProd.isPushout _ _).inr_desc _ _ _
  have e1 : (faceInclBd m k ▷ (Δ[1] : SSet.{u})) =
      (faceSubBdHom m k ▷ (Δ[1] : SSet.{u})) ≫
        ((faceSubBd m k).ι ▷ (Δ[1] : SSet.{u})) := by
    rw [← hH]
    exact comp_whiskerRight _ _ _
  have e2 : (faceSubBdHom m k ▷ (Δ[1] : SSet.{u})) ≫
      ((faceSubBdInv m k ▷ (Δ[1] : SSet.{u})) ≫ lift1 m fk c hbc) =
      lift1 m fk c hbc := by
    rw [← Category.assoc, ← comp_whiskerRight, faceSubBd_hom_inv,
      id_whiskerRight, Category.id_comp]
  calc faceInclBd m k ≫ bdFaceFix m k fk c hbc s hfk
      = faceInclBd m k ≫ (SSet.ι₁ ≫ liftBd m k fk c hbc s hfk) := rfl
    _ = SSet.ι₁ ≫ ((faceInclBd m k ▷ (Δ[1] : SSet.{u})) ≫
          liftBd m k fk c hbc s hfk) := by
        rw [← Category.assoc, ← Category.assoc, SSet.ι₁_comp]
    _ = SSet.ι₁ ≫ lift1 m fk c hbc := by
        rw [e1, Category.assoc, hside]
        exact congrArg (SSet.ι₁ ≫ ·) e2

/-- The ridge map into Λᵏ[m+1], followed by its inclusion into ∂Δ[m+1], equals the boundary map
∂Δ[m]→Δ[m] followed by the k-th face inclusion into ∂Δ[m+1]. -/
private theorem ridge_eq (m : ℕ) (k : Fin (m + 2)) :
    ridgeToHorn m k ≫ Subcomplex.homOfLE (horn_le_boundary k) =
      (SSet.boundary m).ι ≫ faceInclBd m k := by
  apply (cancel_mono (SSet.boundary (m + 1)).ι).mp
  have hle : Subcomplex.homOfLE (horn_le_boundary k) ≫
        (SSet.boundary (m + 1)).ι = (SSet.horn (m + 1) k).ι :=
    Subcomplex.homOfLE_ι _
  calc (ridgeToHorn m k ≫ Subcomplex.homOfLE (horn_le_boundary k)) ≫
          (SSet.boundary (m + 1)).ι
      = ridgeToHorn m k ≫ (Subcomplex.homOfLE (horn_le_boundary k) ≫
          (SSet.boundary (m + 1)).ι) := Category.assoc _ _ _
    _ = ridgeToHorn m k ≫ (SSet.horn (m + 1) k).ι :=
        congrArg (ridgeToHorn m k ≫ ·) hle
    _ = (SSet.boundary m).ι ≫ SSet.stdSimplex.δ k := ridgeToHorn_spec m k
    _ = (SSet.boundary m).ι ≫
          (faceInclBd m k ≫ (SSet.boundary (m + 1)).ι) :=
        congrArg ((SSet.boundary m).ι ≫ ·) (faceInclBd_ι m k).symm
    _ = ((SSet.boundary m).ι ≫ faceInclBd m k) ≫ (SSet.boundary (m + 1)).ι :=
        (Category.assoc _ _ _).symm

/-- Let F be a Kan complex. For m∈ℕ and maps fₖ,c:Δ[m]→F with the same boundary restriction, let H₁
be the cap-zero extension of the constant face fₖ and the boundary null-homotopy induced by c.
For a boundary sphere s:∂Δ[m+1]→F with selected k-th face fₖ, let H_B be the boundary homotopy
extending H₁, and s′ its endpoint-one restriction. The missing k-th face of a horn filler of s′
has constant boundary at the same last-vertex value c(v_last) as f′ₖ. -/
private theorem hornFace_const (m : ℕ) (k : Fin (m + 2))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    (SSet.boundary m).ι ≫
        (SSet.stdSimplex.δ k ≫ hornFill k (bdFaceFix m k fk c hbc s hfk)) =
      SSet.const (c.app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last m))) := by
  have hspec := hornFill_spec k (bdFaceFix m k fk c hbc s hfk)
  have e1 : (SSet.boundary m).ι ≫ SSet.stdSimplex.δ k =
      ridgeToHorn m k ≫ (SSet.horn (m + 1) k).ι := (ridgeToHorn_spec m k).symm
  calc (SSet.boundary m).ι ≫
          (SSet.stdSimplex.δ k ≫ hornFill k (bdFaceFix m k fk c hbc s hfk))
      = ((SSet.boundary m).ι ≫ SSet.stdSimplex.δ k) ≫
          hornFill k (bdFaceFix m k fk c hbc s hfk) :=
        (Category.assoc _ _ _).symm
    _ = (ridgeToHorn m k ≫ (SSet.horn (m + 1) k).ι) ≫
          hornFill k (bdFaceFix m k fk c hbc s hfk) :=
        congrArg (· ≫ hornFill k (bdFaceFix m k fk c hbc s hfk)) e1
    _ = ridgeToHorn m k ≫ ((SSet.horn (m + 1) k).ι ≫
          hornFill k (bdFaceFix m k fk c hbc s hfk)) :=
        Category.assoc _ _ _
    _ = ridgeToHorn m k ≫ (Subcomplex.homOfLE (horn_le_boundary k) ≫
          bdFaceFix m k fk c hbc s hfk) :=
        congrArg (ridgeToHorn m k ≫ ·) hspec.symm
    _ = (ridgeToHorn m k ≫ Subcomplex.homOfLE (horn_le_boundary k)) ≫
          bdFaceFix m k fk c hbc s hfk := (Category.assoc _ _ _).symm
    _ = ((SSet.boundary m).ι ≫ faceInclBd m k) ≫
          bdFaceFix m k fk c hbc s hfk :=
        congrArg (· ≫ bdFaceFix m k fk c hbc s hfk) (ridge_eq m k)
    _ = (SSet.boundary m).ι ≫ (faceInclBd m k ≫
          bdFaceFix m k fk c hbc s hfk) := Category.assoc _ _ _
    _ = (SSet.boundary m).ι ≫ fk' m fk c hbc :=
        congrArg ((SSet.boundary m).ι ≫ ·)
          (face_fix_eq m k fk c hbc s hfk)
    _ = SSet.const (c.app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last m))) :=
        fk'_ridge m fk c hbc

omit [KanComplex F] in
/-- For a map g:Δ[m]→F whose boundary is constant at a vertex y, regard g as a pointed m-simplex
based at y. -/
private noncomputable def facePt {m : ℕ} (g : (Δ[m] : SSet.{u}) ⟶ F)
    (y : F _⦋0⦌) (h : (SSet.boundary m).ι ≫ g = SSet.const y) :
    F.PtSimplex m y where
  map := g
  comm := by
    have hRHS : ∀ (X : SSet.{u}) (z : F _⦋0⦌),
        (SSet.const (X := X) (⟨z, SSet.Subcomplex.mem_ofSimplex_obj z⟩ :
          (SSet.Subcomplex.ofSimplex z : SSet.{u}) _⦋0⦌) ≫
        (SSet.Subcomplex.ofSimplex z).ι) = SSet.const (X := X) z := by
      intro X z
      ext a b
      rfl
    rw [hRHS]
    exact h

/-- A homotopy of pointed m-simplices based at the same vertex y induces a homotopy of their
underlying simplex maps stationary on ∂Δ[m]. -/
private noncomputable def homotopyRelOfPt {m : ℕ} {y : F _⦋0⦌}
    {p q : F.PtSimplex m y} (H : p.Homotopy q) :
    SSet.HomotopyRel p.map q.map (SSet.boundary m) where
  h := H.h
  h₀ := H.h₀
  h₁ := H.h₁
  stationary := fun x hx t => by
    have hpt : H.h.app _ ⟨x, t⟩ =
        (((SSet.boundary m).ι ▷ (Δ[1] : SSet.{u}) ≫ H.h).app _
          ⟨⟨x, hx⟩, t⟩) := rfl
    have hbase : p.map.app _ x =
        ((((SSet.boundary m).ι ≫ p.map).app _)) ⟨x, hx⟩ := rfl
    have hrel := congrArg (fun ψ :
        (((SSet.boundary m : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) ⟶ F) =>
        ψ.app _ ⟨⟨x, hx⟩, t⟩) H.rel
    have hcomm := congrArg (fun ψ : (((SSet.boundary m : SSet.{u})) ⟶ F) =>
      ψ.app _ ⟨x, hx⟩) p.comm
    rw [hpt, hrel]
    exact hcomm.symm.trans (by rfl)

/-- Let F be a Kan complex. For m∈ℕ and maps fₖ,c:Δ[m]→F with the same boundary restriction, let H₁
be the cap-zero extension of the constant face fₖ and the boundary null-homotopy induced by c.
For a boundary sphere s:∂Δ[m+1]→F with selected k-th face fₖ, let H_B be the boundary homotopy
extending H₁, and s′ its endpoint-one restriction. Assume πₙ(F,x) is subsingleton for every n∈ℕ
and every vertex x. The missing k-th face of the horn filler and f′ₖ define pointed m-simplices
based at c(v_last). Their equal homotopy class gives a homotopy relative to ∂Δ[m]. -/
private noncomputable def correctionH (m : ℕ) (k : Fin (m + 2))
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    SSet.HomotopyRel (SSet.stdSimplex.δ k ≫ hornFill k (bdFaceFix m k fk c hbc s hfk))
      (fk' m fk c hbc) (SSet.boundary m) :=
  show SSet.HomotopyRel
    (SSet.stdSimplex.δ k ≫ hornFill k (bdFaceFix m k fk c hbc s hfk))
    (fk' m fk c hbc) (SSet.boundary m) from
  homotopyRelOfPt (SSet.PtSimplex.RelStruct₀.homotopy
    (π.mk_eq_mk_iff.mp ((hπ m
      (c.app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last m)))).elim
      (π.mk (facePt _ _ (hornFace_const m k fk c hbc s hfk)))
      (π.mk (facePt _ _ (fk'_ridge m fk c hbc))))).some)

/-- Let F be a Kan complex. For m∈ℕ and maps fₖ,c:Δ[m]→F with the same boundary restriction, let H₁
be the cap-zero extension of the constant face fₖ and the boundary null-homotopy induced by c.
For a boundary sphere s:∂Δ[m+1]→F with selected k-th face fₖ, let H_B be the boundary homotopy
extending H₁, and s′ its endpoint-one restriction. Assume πₙ(F,x) is subsingleton for every n∈ℕ
and every vertex x. Correct the missing face of the horn filler to f′ₖ using this relative
homotopy, while retaining every other face of that filler. -/
private noncomputable def correctedFace (m : ℕ) (k : Fin (m + 2))
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) : (Δ[m + 1] : SSet.{u}) ⟶ F :=
  (SSet.KanComplex.exists_correct_face_of_HomotopyRel
    (hornFill k (bdFaceFix m k fk c hbc s hfk)) (fk' m fk c hbc)
    (correctionH m k hπ fk c hbc s hfk)).choose

private theorem correctedFace_face (m : ℕ) (k : Fin (m + 2))
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    SSet.stdSimplex.δ k ≫ correctedFace m k hπ fk c hbc s hfk =
      fk' m fk c hbc :=
  (SSet.KanComplex.exists_correct_face_of_HomotopyRel
    (hornFill k (bdFaceFix m k fk c hbc s hfk)) (fk' m fk c hbc)
    (correctionH m k hπ fk c hbc s hfk)).choose_spec.1

private theorem correctedFace_other (m : ℕ) (k : Fin (m + 2))
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) (j : Fin (m + 2)) (hjk : j ≠ k) :
    SSet.stdSimplex.δ j ≫ correctedFace m k hπ fk c hbc s hfk =
      SSet.stdSimplex.δ j ≫ hornFill k (bdFaceFix m k fk c hbc s hfk) :=
  (SSet.KanComplex.exists_correct_face_of_HomotopyRel
    (hornFill k (bdFaceFix m k fk c hbc s hfk)) (fk' m fk c hbc)
    (correctionH m k hπ fk c hbc s hfk)).choose_spec.2 j hjk

/-- For every k∈Fin(m+2), the k-th face map into ∂Δ[m+1] is the standard boundary-face inclusion. -/
private theorem faceInclBd_eq (m : ℕ) (k : Fin (m + 2)) :
    faceInclBd m k = SSet.boundary.ι k := by
  apply (cancel_mono (SSet.boundary (m + 1)).ι).mp
  rw [faceInclBd_ι m k]
  exact (SSet.boundary.ι_ι k).symm

/-- For j≠k in Fin(m+2), the j-th face included through Λᵏ[m+1] and then into ∂Δ[m+1] is the
standard j-th boundary-face map. -/
private theorem hornFaceIncl_eq (m : ℕ) (k : Fin (m + 2)) (j : Fin (m + 2))
    (hjk : j ≠ k) :
    SSet.horn.ι k j hjk ≫ Subcomplex.homOfLE (horn_le_boundary k) =
      SSet.boundary.ι j := by
  apply (cancel_mono (SSet.boundary (m + 1)).ι).mp
  have hle : Subcomplex.homOfLE (horn_le_boundary k) ≫
        (SSet.boundary (m + 1)).ι = (SSet.horn (m + 1) k).ι :=
    Subcomplex.homOfLE_ι _
  calc (SSet.horn.ι k j hjk ≫ Subcomplex.homOfLE (horn_le_boundary k)) ≫
          (SSet.boundary (m + 1)).ι
      = SSet.horn.ι k j hjk ≫ (Subcomplex.homOfLE (horn_le_boundary k) ≫
          (SSet.boundary (m + 1)).ι) := Category.assoc _ _ _
    _ = SSet.horn.ι k j hjk ≫ (SSet.horn (m + 1) k).ι :=
        congrArg (SSet.horn.ι k j hjk ≫ ·) hle
    _ = SSet.stdSimplex.δ j := SSet.horn.ι_ι _ _ _
    _ = SSet.boundary.ι j ≫ (SSet.boundary (m + 1)).ι :=
        (SSet.boundary.ι_ι j).symm

/-- Let F be a Kan complex. For m∈ℕ and maps fₖ,c:Δ[m]→F with the same boundary restriction, let H₁
be the cap-zero extension of the constant face fₖ and the boundary null-homotopy induced by c.
For a boundary sphere s:∂Δ[m+1]→F with selected k-th face fₖ, let H_B be the boundary homotopy
extending H₁, and s′ its endpoint-one restriction. Assume πₙ(F,x) is subsingleton for every n∈ℕ
and every vertex x. The corrected (m+1)-simplex restricts on its entire boundary to s′. -/
private theorem correctedFace_extends (m : ℕ) (k : Fin (m + 2))
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    (SSet.boundary (m + 1)).ι ≫ correctedFace m k hπ fk c hbc s hfk =
      bdFaceFix m k fk c hbc s hfk := by
  refine SSet.boundary.hom_ext (fun j => ?_)
  by_cases hjk : j = k
  · rw [hjk]
    have hface := correctedFace_face m k hπ fk c hbc s hfk
    calc SSet.boundary.ι k ≫ ((SSet.boundary (m + 1)).ι ≫
            correctedFace m k hπ fk c hbc s hfk)
        = SSet.stdSimplex.δ k ≫ correctedFace m k hπ fk c hbc s hfk := by
          rw [← Category.assoc, SSet.boundary.ι_ι]
      _ = fk' m fk c hbc := hface
      _ = faceInclBd m k ≫ bdFaceFix m k fk c hbc s hfk :=
          (face_fix_eq m k fk c hbc s hfk).symm
      _ = SSet.boundary.ι k ≫ bdFaceFix m k fk c hbc s hfk :=
          congrArg (· ≫ bdFaceFix m k fk c hbc s hfk) (faceInclBd_eq m k)
  · have hother := correctedFace_other m k hπ fk c hbc s hfk j hjk
    have hspec := hornFill_spec k (bdFaceFix m k fk c hbc s hfk)
    have hδ : SSet.stdSimplex.δ j =
        SSet.horn.ι k j hjk ≫ (SSet.horn (m + 1) k).ι :=
      (SSet.horn.ι_ι k j hjk).symm
    calc SSet.boundary.ι j ≫ ((SSet.boundary (m + 1)).ι ≫
            correctedFace m k hπ fk c hbc s hfk)
        = SSet.stdSimplex.δ j ≫ correctedFace m k hπ fk c hbc s hfk := by
          rw [← Category.assoc, SSet.boundary.ι_ι]
      _ = SSet.stdSimplex.δ j ≫ hornFill k (bdFaceFix m k fk c hbc s hfk) :=
          hother
      _ = (SSet.horn.ι k j hjk ≫ (SSet.horn (m + 1) k).ι) ≫
            hornFill k (bdFaceFix m k fk c hbc s hfk) :=
          congrArg (· ≫ hornFill k (bdFaceFix m k fk c hbc s hfk)) hδ
      _ = SSet.horn.ι k j hjk ≫ ((SSet.horn (m + 1) k).ι ≫
            hornFill k (bdFaceFix m k fk c hbc s hfk)) :=
          Category.assoc _ _ _
      _ = SSet.horn.ι k j hjk ≫ (Subcomplex.homOfLE (horn_le_boundary k) ≫
            bdFaceFix m k fk c hbc s hfk) :=
          congrArg (SSet.horn.ι k j hjk ≫ ·) hspec.symm
      _ = (SSet.horn.ι k j hjk ≫ Subcomplex.homOfLE (horn_le_boundary k)) ≫
            bdFaceFix m k fk c hbc s hfk := (Category.assoc _ _ _).symm
      _ = SSet.boundary.ι j ≫ bdFaceFix m k fk c hbc s hfk :=
          congrArg (· ≫ bdFaceFix m k fk c hbc s hfk)
            (hornFaceIncl_eq m k j hjk)

omit [KanComplex F] in
/-- In any simplicial degree d, a pair (y,t)∈X_d×Δ[1]_d with t in the vertex-one face equals the
endpoint-one image ι₁(y). -/
private theorem iota_one_pair {X : SSet.{u}} {d : ℕ}
    (y : X.obj (Opposite.op ⦋d⦌))
    (t : (Δ[1] : SSet.{u}).obj (Opposite.op ⦋d⦌))
    (ht : t ∈ (SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).obj
      (Opposite.op ⦋d⦌)) :
    (⟨y, (((SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).ι.app
        (Opposite.op ⦋d⦌)) ⟨t, ht⟩)⟩ :
      (X ⊗ (Δ[1] : SSet.{u})).obj (Opposite.op ⦋d⦌)) =
      SSet.ι₁.app (Opposite.op ⦋d⦌) y := by
  refine Prod.ext rfl ?_
  dsimp only
  change t = _
  ext a
  have ht1 : ∀ a, t a = (1 : Fin 2) := fun a =>
    Finset.mem_singleton.mp ((SSet.stdSimplex.mem_face_iff _ _).mp ht a)
  simp only [ht1]
  congr 1

/-- Let F be a Kan complex. For m∈ℕ and maps fₖ,c:Δ[m]→F with the same boundary restriction, let H₁
be the cap-zero extension of the constant face fₖ and the boundary null-homotopy induced by c.
For a boundary sphere s:∂Δ[m+1]→F with selected k-th face fₖ, let H_B be the boundary homotopy
extending H₁, and s′ its endpoint-one restriction. Assume πₙ(F,x) is subsingleton for every n∈ℕ
and every vertex x. The corrected filler, constant on the cap-one side, agrees with H_B on
∂Δ[m+1]×{1}, because both restrict there to s′. -/
private theorem agreeCap (m : ℕ) (k : Fin (m + 2))
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    ((SSet.boundary (m + 1)).ι ▷
        ((SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u})) ≫
      (fst _ _ ≫ correctedFace m k hπ fk c hbc s hfk) =
      (((∂Δ[m + 1] : SSet.{u}) ◁
          (SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).ι) ≫
        liftBd m k fk c hbc s hfk) := by
  ext n ⟨⟨a, ha⟩, ⟨t, ht⟩⟩
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = Opposite.op ⦋d⦌ := ⟨n.unop.len, rfl⟩
  have hpair : (⟨⟨a, ha⟩, ((SSet.stdSimplex.face {1} :
      (Δ[1] : SSet.{u}).Subcomplex).ι.app _ ⟨t, ht⟩)⟩ :
      ((((∂Δ[m + 1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})).obj
        (Opposite.op ⦋d⦌)))) =
      SSet.ι₁.app _ (⟨a, ha⟩ : ((∂Δ[m + 1] : SSet.{u}).obj
        (Opposite.op ⦋d⦌))) :=
    iota_one_pair (X := (∂Δ[m + 1] : SSet.{u})) (d := d)
      (⟨a, ha⟩ : ((∂Δ[m + 1] : SSet.{u}).obj (Opposite.op ⦋d⦌))) t ht
  have hH1 : (liftBd m k fk c hbc s hfk).app _ ⟨⟨a, ha⟩,
      ((SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).ι.app _
        ⟨t, ht⟩)⟩ =
      (bdFaceFix m k fk c hbc s hfk).app _ ⟨a, ha⟩ := by
    calc (liftBd m k fk c hbc s hfk).app _ ⟨⟨a, ha⟩,
            ((SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).ι.app _
              ⟨t, ht⟩)⟩
        = (liftBd m k fk c hbc s hfk).app _
            (SSet.ι₁.app _ ⟨a, ha⟩) := by rw [← hpair]
      _ = (SSet.ι₁ ≫ liftBd m k fk c hbc s hfk).app _ ⟨a, ha⟩ := rfl
      _ = (bdFaceFix m k fk c hbc s hfk).app _ ⟨a, ha⟩ := rfl
  have hgoal : ((((SSet.boundary (m + 1)).ι ▷
      ((SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u})) ≫
      (fst _ _ ≫ correctedFace m k hπ fk c hbc s hfk)).app _
      ⟨⟨a, ha⟩, ⟨t, ht⟩⟩) =
      ((((∂Δ[m + 1] : SSet.{u}) ◁
        (SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).ι) ≫
        liftBd m k fk c hbc s hfk).app _ ⟨⟨a, ha⟩, ⟨t, ht⟩⟩) := by
    calc ((((SSet.boundary (m + 1)).ι ▷
        ((SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u})) ≫
        (fst _ _ ≫ correctedFace m k hπ fk c hbc s hfk)).app _
        ⟨⟨a, ha⟩, ⟨t, ht⟩⟩)
        = (correctedFace m k hπ fk c hbc s hfk).app _ a := rfl
      _ = (((SSet.boundary (m + 1)).ι ≫
          correctedFace m k hπ fk c hbc s hfk).app _ ⟨a, ha⟩) := rfl
      _ = ((bdFaceFix m k fk c hbc s hfk).app _ ⟨a, ha⟩) := by
          rw [correctedFace_extends m k hπ fk c hbc s hfk]
      _ = (liftBd m k fk c hbc s hfk).app _ ⟨⟨a, ha⟩,
          ((SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).ι.app _
            ⟨t, ht⟩)⟩ := hH1.symm
      _ = _ := rfl
  exact hgoal

/-- Let F be a Kan complex. For m∈ℕ and maps fₖ,c:Δ[m]→F with the same boundary restriction, let H₁
be the cap-zero extension of the constant face fₖ and the boundary null-homotopy induced by c.
For a boundary sphere s:∂Δ[m+1]→F with selected k-th face fₖ, let H_B be the boundary homotopy
extending H₁, and s′ its endpoint-one restriction. Assume πₙ(F,x) is subsingleton for every n∈ℕ
and every vertex x. Glue the boundary homotopy H_B to the constant corrected filler on cap one,
obtaining a map on (∂Δ[m+1]×Δ[1])∪(Δ[m+1]×{1}). -/
private noncomputable def gCap (m : ℕ) (k : Fin (m + 2))
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    (((capSubcomplex (m + 1)) : SSet.{u})) ⟶ F :=
  (Subcomplex.unionProd.isPushout (SSet.boundary (m + 1))
    (SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex)).desc
    (fst _ _ ≫ correctedFace m k hπ fk c hbc s hfk)
    (liftBd m k fk c hbc s hfk)
    (agreeCap m k hπ fk c hbc s hfk)

/-- Let F be a Kan complex. For m∈ℕ and maps fₖ,c:Δ[m]→F with the same boundary restriction, let H₁
be the cap-zero extension of the constant face fₖ and the boundary null-homotopy induced by c.
For a boundary sphere s:∂Δ[m+1]→F with selected k-th face fₖ, let H_B be the boundary homotopy
extending H₁, and s′ its endpoint-one restriction. Assume πₙ(F,x) is subsingleton for every n∈ℕ
and every vertex x. The cap-one map extends to a cylinder map Δ[m+1]×Δ[1]→F. -/
private noncomputable def liftCap (m : ℕ) (k : Fin (m + 2))
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    (Δ[m + 1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ F :=
  (SSet.anodyneExtensions.exists_lift_of_isFibrant
    (gCap m k hπ fk c hbc s hfk) (cap_mem_anodyneExtensions (m + 1))).choose

private theorem liftCap_spec (m : ℕ) (k : Fin (m + 2))
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    (((SSet.boundary (m + 1)).unionProd
      (SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex)).ι ≫
      liftCap m k hπ fk c hbc s hfk) =
      gCap m k hπ fk c hbc s hfk :=
  (SSet.anodyneExtensions.exists_lift_of_isFibrant
    (gCap m k hπ fk c hbc s hfk) (cap_mem_anodyneExtensions (m + 1))).choose_spec

/-- Let F be a Kan complex. For m∈ℕ and maps fₖ,c:Δ[m]→F with the same boundary restriction, let H₁
be the cap-zero extension of the constant face fₖ and the boundary null-homotopy induced by c.
For a boundary sphere s:∂Δ[m+1]→F with selected k-th face fₖ, let H_B be the boundary homotopy
extending H₁, and s′ its endpoint-one restriction. Assume πₙ(F,x) is subsingleton for every n∈ℕ
and every vertex x. Restricting the cap-one extension at endpoint zero gives t:Δ[m+1]→F with
boundary s, the original sphere. -/
private theorem fillerOfCorrected (m : ℕ) (k : Fin (m + 2))
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x))
    (fk c : (Δ[m] : SSet.{u}) ⟶ F)
    (hbc : (SSet.boundary m).ι ≫ c = (SSet.boundary m).ι ≫ fk)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F)
    (hfk : fk = faceInclBd m k ≫ s) :
    ∃ t : (Δ[m + 1] : SSet.{u}) ⟶ F, (SSet.boundary (m + 1)).ι ≫ t = s := by
  refine ⟨SSet.ι₀ ≫ liftCap m k hπ fk c hbc s hfk, ?_⟩
  have hside : ((SSet.boundary (m + 1)).ι ▷ (Δ[1] : SSet.{u})) ≫
      liftCap m k hπ fk c hbc s hfk = liftBd m k fk c hbc s hfk := by
    rw [← Subcomplex.unionProd.ι₂_ι (SSet.boundary (m + 1))
      (SSet.stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex),
      Category.assoc, liftCap_spec m k hπ fk c hbc s hfk]
    exact (Subcomplex.unionProd.isPushout _ _).inr_desc _ _ _
  calc (SSet.boundary (m + 1)).ι ≫
          (SSet.ι₀ ≫ liftCap m k hπ fk c hbc s hfk)
      = SSet.ι₀ ≫ (((SSet.boundary (m + 1)).ι ▷ (Δ[1] : SSet.{u})) ≫
          liftCap m k hπ fk c hbc s hfk) := by
        rw [← Category.assoc, ← Category.assoc, SSet.ι₀_comp]
    _ = SSet.ι₀ ≫ liftBd m k fk c hbc s hfk :=
        congrArg (SSet.ι₀ ≫ ·) hside
    _ = s := liftBd_zero m k fk c hbc s hfk

/-- Let F be a Kan complex. Assume all based homotopy sets πₙ(F,x) are subsingleton. If every map
∂Δ[m]→F extends to Δ[m], then every map ∂Δ[m+1]→F extends to Δ[m+1]. -/
private theorem stepAux (m : ℕ)
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x))
    (IH : ∀ s : (∂Δ[m] : SSet.{u}) ⟶ F,
      ∃ t : Δ[m] ⟶ F, (SSet.boundary m).ι ≫ t = s)
    (s : (∂Δ[m + 1] : SSet.{u}) ⟶ F) :
    ∃ t : (Δ[m + 1] : SSet.{u}) ⟶ F, (SSet.boundary (m + 1)).ι ≫ t = s := by
  obtain ⟨k⟩ : Nonempty (Fin (m + 2)) := ⟨⟨0, by omega⟩⟩
  obtain ⟨c, hc⟩ := IH ((SSet.boundary m).ι ≫ faceInclBd m k ≫ s)
  exact fillerOfCorrected m k hπ (faceInclBd m k ≫ s) c hc s rfl

/-- Let F be a Kan complex. A chosen vertex x₀ and subsingleton πₙ(F,x) for every degree n and
vertex x give a filler for every boundary sphere ∂Δ[n]→F, including n=0. -/
private theorem existsFillerAux (x₀ : F _⦋0⦌)
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x)) : ∀ (n : ℕ)
    (s : (∂Δ[n] : SSet.{u}) ⟶ F),
    ∃ t : Δ[n] ⟶ F, (SSet.boundary n).ι ≫ t = s := by
  intro n
  induction n with
  | zero => intro s; exact filler_zero x₀ s
  | succ m IHm => intro s; exact stepAux m hπ IHm s

/-- Let F be a Kan complex with a chosen vertex x₀. Assume πₙ(F,x) is subsingleton for every n∈ℕ and
every vertex x. Then each s:∂Δ[n]→F extends to t:Δ[n]→F with boundary restriction equal to s,
for all n including zero. -/
theorem exists_boundary_filler_of_subsingleton_pi (x₀ : F _⦋0⦌)
    (hπ : ∀ (n : ℕ) (x : F _⦋0⦌), Subsingleton (π n F x))
    {n : ℕ} (s : (∂Δ[n] : SSet.{u}) ⟶ F) :
    ∃ t : Δ[n] ⟶ F, (SSet.boundary n).ι ≫ t = s :=
  existsFillerAux x₀ hπ n s

end SSet.KanComplex
