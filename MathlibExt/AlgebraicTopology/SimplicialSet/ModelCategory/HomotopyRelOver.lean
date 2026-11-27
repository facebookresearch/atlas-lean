/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetDeformationRetract

/-!
# Relative simplicial homotopies over a base

For X,Y,S in universe u, p:Y→S, f,g:X→Y and A⊆X, a homotopy relative to A over p is a map
H:X⊗Δ[1]→Y with endpoints f,g, stationary on A, and H≫p=pr_X≫f≫p. It implies equality of the two
endpoint base maps. The constant homotopy is reflexive for every p. If p is a simplicial
fibration, outer-horn filling reverses these homotopies and inner-horn filling composes them.

Reference: Goerss and Jardine, Simplicial Homotopy Theory, Chapter I.
-/

@[expose] public section

open CategoryTheory Simplicial SSet Limits MonoidalCategory CartesianMonoidalCategory

universe u

namespace SSet

/-- For X,Y,S in universe u, p:Y→S, f,g:X→Y and subcomplex A⊆X, a relative homotopy over p is a map
H:X⊗Δ[1]→Y with ι₀≫H=f and ι₁≫H=g, stationary on A, and H≫p=pr_X≫f≫p. Stationarity means
H_n(a,t)=f_n(a) for a∈A_n and every interval simplex t; the over-base equation implies f≫p=g≫p. -/
structure HomotopyRelOver {X Y S : SSet.{u}} (p : Y ⟶ S) (f g : X ⟶ Y)
    (A : X.Subcomplex) where
  /-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
  satisfy H≫p=pr_X≫f≫p. The relative-homotopy component keeps H and its two endpoints, with
  H_n(a,t)=f_n(a) for every simplex a∈A and every interval simplex t. -/
  toHomotopyRel : HomotopyRel f g A
  /-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
  satisfy H≫p=pr_X≫f≫p. The over-base component is the equality H≫p=pr_X≫f≫p of maps X⊗Δ[1]→S. -/
  over : toHomotopyRel.h ≫ p = fst _ _ ≫ (f ≫ p)

namespace HomotopyRelOver

variable {X Y S : SSet.{u}} {p : Y ⟶ S} {f g : X ⟶ Y} {A : X.Subcomplex}

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. Its cylinder map is H:X⊗Δ[1]→Y, inherited from the underlying relative
homotopy. -/
def h (H : HomotopyRelOver p f g A) : X ⊗ (Δ[1] : SSet.{u}) ⟶ Y :=
  H.toHomotopyRel.h

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. The cylinder satisfies ι₀≫H=f:X→Y. -/
@[reassoc (attr := simp)]
lemma h₀ (H : HomotopyRelOver p f g A) : SSet.ι₀ ≫ H.h = f :=
  H.toHomotopyRel.h₀

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. The cylinder satisfies ι₁≫H=g:X→Y. -/
@[reassoc (attr := simp)]
lemma h₁ (H : HomotopyRelOver p f g A) : SSet.ι₁ ≫ H.h = g :=
  H.toHomotopyRel.h₁

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. For any simplex object c, a∈A_c and t∈Δ[1]_c, H_c(a,t)=f_c(a). -/
lemma stationary (H : HomotopyRelOver p f g A) {n : SimplexCategoryᵒᵖ}
    {x : X.obj n} (hx : x ∈ A.obj n) (t : (Δ[1] : SSet.{u}).obj n) :
    H.h.app n ⟨x, t⟩ = f.app n x :=
  H.toHomotopyRel.stationary x hx t

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. Its projection to S is H≫p=pr_X≫f≫p. -/
@[reassoc]
lemma over_eq (H : HomotopyRelOver p f g A) :
    H.h ≫ p = fst _ _ ≫ (f ≫ p) :=
  H.over

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. Its endpoint maps satisfy f≫p=g≫p:X→S. -/
lemma map_eq (H : HomotopyRelOver p f g A) : f ≫ p = g ≫ p := by
  have hg1 : (SSet.ι₁ ≫ H.toHomotopyRel.h) ≫ p = g ≫ p := by
    rw [H.toHomotopyRel.h₁]
  have hg2 : (SSet.ι₁ ≫ H.toHomotopyRel.h) ≫ p = f ≫ p := by
    calc (SSet.ι₁ ≫ H.toHomotopyRel.h) ≫ p
        = SSet.ι₁ ≫ (H.toHomotopyRel.h ≫ p) := by rw [Category.assoc]
      _ = SSet.ι₁ ≫ (fst _ _ ≫ (f ≫ p)) := by rw [H.over]
      _ = (SSet.ι₁ ≫ fst _ _) ≫ (f ≫ p) := by rw [Category.assoc]
      _ = f ≫ p := by rw [SSet.ι₁_fst, Category.id_comp]
  exact hg2.symm.trans hg1

/-- For f:X→Y, p:Y→S and A⊆X in universe u, the constant cylinder pr_X≫f gives a relative homotopy
f≃f over p, stationary on A. Its base composite is pr_X≫f≫p. -/
noncomputable def refl (f : X ⟶ Y) (A : X.Subcomplex) (p : Y ⟶ S) :
    HomotopyRelOver p f f A where
  toHomotopyRel := HomotopyRel.refl f A
  over := by
    calc (HomotopyRel.refl f A).h ≫ p
        = (fst _ _ ≫ f) ≫ p := rfl
      _ = fst _ _ ≫ (f ≫ p) := by rw [Category.assoc]

end HomotopyRelOver

end SSet

end

public section

open CategoryTheory Simplicial SSet Limits MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace SSet

namespace HomotopyRelOver

variable {X Y S : SSet.{u}} {p : Y ⟶ S} {f g : X ⟶ Y} {A : X.Subcomplex}

/-!
## The outer horn for symmetry

For H:f≃g, the 02 edge of Λ²₂ is the constant homotopy at g and the 12 edge is H. They agree at
vertex 2. Filling this outer horn gives the missing 01 edge from g to f.
-/

/-- For X in universe u, the two edges 02 and 12 of Λ²₂ meet at vertex 2. Tensoring this face
pushout with X gives the corresponding pushout presentation of X⊗Λ²₂. -/
private theorem horn₂₂TensorLeftIsPushout (X : SSet.{u}) :
    IsPushout
      (X ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1]))
      (X ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1]))
      (X ◁ SSet.horn₂₂.ι₀₂)
      (X ◁ SSet.horn₂₂.ι₁₂) := by
  have : PreservesColimit
      (span (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1])
        (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1]))
      (MonoidalCategory.tensorLeft (X : SSet.{u})) :=
    inferInstance
  exact (MonoidalCategory.tensorLeft (X : SSet.{u})).map_isPushout
    SSet.horn₂₂.isPushout

/-- For g:X→Y in universe u, the constant cylinder C_g:X⊗Δ[1]→Y is pr_X≫g. It is the map on the 02
face of the symmetry horn. -/
private noncomputable def symmHornConst {X Y : SSet.{u}} (g : X ⟶ Y) :
    X ⊗ (Δ[1] : SSet.{u}) ⟶ Y :=
  fst _ _ ≫ g

/-- For g:X→Y in universe u, ι₁≫C_g=g, where C_g=pr_X≫g. -/
@[reassoc (attr := simp)]
private lemma symmHornConst_ι₁ {X Y : SSet.{u}} (g : X ⟶ Y) :
    SSet.ι₁ ≫ (symmHornConst g : X ⊗ Δ[1] ⟶ Y) = g := by
  simp [symmHornConst]

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. Its endpoint-1 restriction is ι₁≫H=g. -/
@[reassoc (attr := simp)]
private lemma symmHornH_ι₁ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    SSet.ι₁ ≫ H.h = g :=
  H.h₁

/-- For g:X→Y in universe u, restricting C_g along id_X⊗δ₀:X⊗Δ[0]→X⊗Δ[1] gives pr_X≫g:X⊗Δ[0]→Y. -/
private lemma symmHornConst_δ₀ {X Y : SSet.{u}} (g : X ⟶ Y) :
    (X ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1])) ≫
        (symmHornConst g : X ⊗ Δ[1] ⟶ Y) =
      fst _ _ ≫ g := by
  ext n ⟨x, _t₀⟩
  rfl

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. Restricting H along id_X⊗δ₀ gives pr_X≫g:X⊗Δ[0]→Y. -/
private lemma symmHornH_δ₀ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    (X ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1])) ≫ H.h =
      fst _ _ ≫ g := by
  ext n ⟨x, t₀⟩
  have hδ : stdSimplex.δ (0 : Fin 2) =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
    stdSimplex.δ_zero_eq_const
  have h_pair :
      (X ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1])).app n ⟨x, t₀⟩ =
        SSet.ι₁.app n x := by
    have h₁ : (X ◁ (stdSimplex.δ (0 : Fin 2))).app n ⟨x, t₀⟩ =
        ⟨x, (stdSimplex.δ (0 : Fin 2)).app n t₀⟩ := rfl
    have h₂ : (stdSimplex.δ (0 : Fin 2)).app n t₀ =
        (SSet.const (stdSimplex.obj₀Equiv.symm 1) : X ⟶ Δ[1]).app n x := by
      rw [hδ]
      rfl
    have h₃ : SSet.ι₁.app n x =
        ⟨x, (SSet.const (stdSimplex.obj₀Equiv.symm 1) : X ⟶ Δ[1]).app n x⟩ := rfl
    rw [h₁, h₂, ← h₃]
  calc H.h.app n ((X ◁ (stdSimplex.δ (0 : Fin 2))).app n ⟨x, t₀⟩)
      = H.h.app n (SSet.ι₁.app n x) := by rw [h_pair]
    _ = (SSet.ι₁ ≫ H.h).app n x := rfl
    _ = g.app n x := by rw [H.h₁]
    _ = (fst _ _ ≫ g).app n ⟨x, t₀⟩ := rfl

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. The 02 face C_g and the 12 face H agree on the common vertex 2, each
giving g after the right zero-simplex unit identification. -/
private lemma symmHornFaces_agree {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    (X ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1])) ≫
        (symmHornConst g : X ⊗ Δ[1] ⟶ Y) =
      (X ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1])) ≫ H.h := by
  rw [symmHornConst_δ₀, symmHornH_δ₀]

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. The two compatible faces define J:X⊗Λ²₂→Y, with 02 face C_g and 12 face H. -/
private noncomputable def symmHornMap {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    X ⊗ (SSet.horn 2 (2 : Fin 3) : SSet.{u}) ⟶ Y :=
  (horn₂₂TensorLeftIsPushout X).desc
    (symmHornConst g) H.h (symmHornFaces_agree H)

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. For J:X⊗Λ²₂→Y, restricting to its 02 face gives C_g=pr_X≫g. -/
@[reassoc]
private lemma symmHornMap_ι₀₂ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    (X ◁ SSet.horn₂₂.ι₀₂) ≫ symmHornMap H = symmHornConst g :=
  (horn₂₂TensorLeftIsPushout X).inl_desc _ _ _

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. For J:X⊗Λ²₂→Y, restricting to its 12 face gives H. -/
@[reassoc]
private lemma symmHornMap_ι₁₂ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    (X ◁ SSet.horn₂₂.ι₁₂) ≫ symmHornMap H = H.h :=
  (horn₂₂TensorLeftIsPushout X).inr_desc _ _ _

/-!
## Stationarity on the relative subcomplex

The symmetry lifting domain is U₂=(X⊗Λ²₂)∪(A⊗Δ[2]). On A⊗Δ[2] use pr_A≫A.ι≫f. It agrees with the
horn map on A⊗Λ²₂ because H is stationary and A.ι≫f=A.ι≫g.
-/

/-- For p:Y→S and f:X→Y in universe u, define Q:X⊗Δ[2]→S by Q=pr_X≫f≫p. -/
private noncomputable def symmBaseMap {X Y S : SSet.{u}} (p : Y ⟶ S) (f : X ⟶ Y) :
    X ⊗ (Δ[2] : SSet.{u}) ⟶ S :=
  fst X _ ≫ f ≫ p

/-- For f:X→Y and A⊆X in universe u, define R:A⊗Δ[2]→Y by R=pr_A≫A.ι≫f. -/
private noncomputable def symmStationaryFace {X Y : SSet.{u}} (f : X ⟶ Y)
    (A : X.Subcomplex) :
    (A : SSet.{u}) ⊗ (Δ[2] : SSet.{u}) ⟶ Y :=
  fst (A : SSet.{u}) _ ≫ A.ι ≫ f

/-- For p:Y→S, f:X→Y and A⊆X in universe u, R≫p=(A.ι⊗id_{Δ[2]})≫Q, where R=pr_A≫A.ι≫f and
Q=pr_X≫f≫p. -/
private lemma symmStationaryFace_over {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f : X ⟶ Y} {A : X.Subcomplex} :
    symmStationaryFace f A ≫ p = (A.ι ▷ (Δ[2] : SSet.{u})) ≫ symmBaseMap p f := by
  calc symmStationaryFace f A ≫ p
      = (fst (A : SSet.{u}) (Δ[2] : SSet.{u}) ≫ A.ι) ≫ f ≫ p := by
        simp only [symmStationaryFace, Category.assoc]
    _ = (A.ι ▷ (Δ[2] : SSet.{u}) ≫ fst X (Δ[2] : SSet.{u})) ≫ f ≫ p := by
        rw [← whiskerRight_fst (f := A.ι) (Z := (Δ[2] : SSet.{u}))]
    _ = (A.ι ▷ (Δ[2] : SSet.{u})) ≫ symmBaseMap p f := by
        simp only [symmBaseMap, Category.assoc]

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. Their restrictions satisfy A.ι≫f=A.ι≫g. -/
private lemma stationary_ends {X Y S : SSet.{u}} {p : Y ⟶ S} {f g : X ⟶ Y}
    {A : X.Subcomplex} (H : HomotopyRelOver p f g A) :
    A.ι ≫ f = A.ι ≫ g := by
  ext n ⟨x, hx⟩
  have h_app_g : H.h.app n (SSet.ι₁.app n x) = g.app n x := by
    calc H.h.app n (SSet.ι₁.app n x)
        = (SSet.ι₁ ≫ H.h).app n x := rfl
      _ = g.app n x := by rw [H.h₁]
  have h_fst : (SSet.ι₁.app n x).1 = x := by
    simp
  have h_pair : SSet.ι₁.app n x = ⟨x, (SSet.ι₁.app n x).2⟩ := by
    apply Prod.ext
    · exact h_fst
    · rfl
  have h_stat : H.h.app n (SSet.ι₁.app n x) = f.app n x := by
    calc H.h.app n (SSet.ι₁.app n x)
        = H.h.app n ⟨x, (SSet.ι₁.app n x).2⟩ := by rw [h_pair]
      _ = f.app n x := H.stationary (x := x) hx (t := (SSet.ι₁.app n x).2)
  calc (A.ι ≫ f).app n ⟨x, hx⟩
      = f.app n x := rfl
    _ = H.h.app n (SSet.ι₁.app n x) := h_stat.symm
    _ = g.app n x := h_app_g
    _ = (A.ι ≫ g).app n ⟨x, hx⟩ := rfl

/-- For f:X→Y and A⊆X in universe u, R=pr_A≫A.ι≫f on A⊗Δ[2] restricts along the 02 edge to
pr_A≫A.ι≫f:A⊗Δ[1]→Y. -/
private lemma symmStationaryFace_ι₀₂ {X Y : SSet.{u}} (f : X ⟶ Y)
    (A : X.Subcomplex) :
    (A : SSet.{u}) ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫
        symmStationaryFace f A =
      fst _ _ ≫ A.ι ≫ f := by
  calc (A : SSet.{u}) ◁ stdSimplex.δ (1 : Fin 3) ≫ symmStationaryFace f A
      = (A : SSet.{u}) ◁ stdSimplex.δ (1 : Fin 3) ≫
          (fst (A : SSet.{u}) (Δ[2] : SSet.{u}) ≫ A.ι ≫ f) := rfl
    _ = ((A : SSet.{u}) ◁ stdSimplex.δ (1 : Fin 3) ≫
          fst (A : SSet.{u}) (Δ[2] : SSet.{u})) ≫ A.ι ≫ f := by
        simp only [Category.assoc]
    _ = fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ f := by
        rw [whiskerLeft_fst]

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. The restriction to A⊗Δ[1] of J on its 02 face is pr_A≫A.ι≫g. -/
private lemma symmHornMap_ι₀₂_restrict {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    (A : SSet.{u}) ◁ SSet.horn₂₂.ι₀₂ ≫
        (A.ι ▷ (SSet.horn 2 (2 : Fin 3) : SSet.{u})) ≫ symmHornMap H =
      fst _ _ ≫ A.ι ≫ g := by
  calc (A : SSet.{u}) ◁ SSet.horn₂₂.ι₀₂ ≫
          (A.ι ▷ (SSet.horn 2 (2 : Fin 3) : SSet.{u})) ≫ symmHornMap H
      = ((A : SSet.{u}) ◁ SSet.horn₂₂.ι₀₂ ≫
            A.ι ▷ (SSet.horn 2 (2 : Fin 3) : SSet.{u})) ≫ symmHornMap H := by
        simp only [Category.assoc]
    _ = ((A.ι ▷ (Δ[1] : SSet.{u})) ≫ X ◁ SSet.horn₂₂.ι₀₂) ≫ symmHornMap H := by
        rw [whisker_exchange]
    _ = A.ι ▷ (Δ[1] : SSet.{u}) ≫ (X ◁ SSet.horn₂₂.ι₀₂ ≫ symmHornMap H) := by
        simp only [Category.assoc]
    _ = A.ι ▷ (Δ[1] : SSet.{u}) ≫ symmHornConst g := by
        rw [symmHornMap_ι₀₂]
    _ = A.ι ▷ (Δ[1] : SSet.{u}) ≫ (fst X (Δ[1] : SSet.{u}) ≫ g) := rfl
    _ = (A.ι ▷ (Δ[1] : SSet.{u}) ≫ fst X (Δ[1] : SSet.{u})) ≫ g := by
        simp only [Category.assoc]
    _ = (fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι) ≫ g := by
        rw [whiskerRight_fst]
    _ = fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ g := by
        simp only [Category.assoc]

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. On A⊗Δ[1], the 02 restriction of J equals the 02 restriction of
R=pr_A≫A.ι≫f, using A.ι≫f=A.ι≫g. -/
private lemma symmHornMap_ι₀₂_stationaryAgree {X Y S : SSet.{u}}
    {p : Y ⟶ S} {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    (A : SSet.{u}) ◁ SSet.horn₂₂.ι₀₂ ≫
        (A.ι ▷ (SSet.horn 2 (2 : Fin 3) : SSet.{u})) ≫ symmHornMap H =
      (A : SSet.{u}) ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫
        symmStationaryFace f A := by
  have hHorn := symmHornMap_ι₀₂_restrict H
  have hStat := symmStationaryFace_ι₀₂ (X := X) (Y := Y) f A
  have hg : A.ι ≫ g = A.ι ≫ f := (stationary_ends H).symm
  calc (A : SSet.{u}) ◁ SSet.horn₂₂.ι₀₂ ≫
          (A.ι ▷ (SSet.horn 2 (2 : Fin 3) : SSet.{u})) ≫ symmHornMap H
      = fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ g := hHorn
    _ = fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ f := by
        rw [hg]
    _ = (A : SSet.{u}) ◁ stdSimplex.δ (1 : Fin 3) ≫ symmStationaryFace f A := by
        rw [← hStat]

/-- For f:X→Y and A⊆X in universe u, R=pr_A≫A.ι≫f on A⊗Δ[2] restricts along the 12 edge to
pr_A≫A.ι≫f:A⊗Δ[1]→Y. -/
private lemma symmStationaryFace_ι₁₂ {X Y : SSet.{u}} (f : X ⟶ Y)
    (A : X.Subcomplex) :
    (A : SSet.{u}) ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫
        symmStationaryFace f A =
      fst _ _ ≫ A.ι ≫ f := by
  calc (A : SSet.{u}) ◁ stdSimplex.δ (0 : Fin 3) ≫ symmStationaryFace f A
      = (A : SSet.{u}) ◁ stdSimplex.δ (0 : Fin 3) ≫
          (fst (A : SSet.{u}) (Δ[2] : SSet.{u}) ≫ A.ι ≫ f) := rfl
    _ = ((A : SSet.{u}) ◁ stdSimplex.δ (0 : Fin 3) ≫
          fst (A : SSet.{u}) (Δ[2] : SSet.{u})) ≫ A.ι ≫ f := by
        simp only [Category.assoc]
    _ = fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ f := by
        rw [whiskerLeft_fst]

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. Its subcomplex restriction is (A.ι⊗id_{Δ[1]})≫H=pr_A≫A.ι≫f. -/
private lemma symmHornH_stationary {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    (A.ι ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst _ _ ≫ A.ι ≫ f := by
  ext n ⟨⟨x, hx⟩, t⟩
  calc (A.ι ▷ (Δ[1] : SSet.{u}) ≫ H.h).app n ⟨⟨x, hx⟩, t⟩
      = H.h.app n ⟨x, t⟩ := rfl
    _ = f.app n x := H.stationary hx t
    _ = (fst _ _ ≫ A.ι ≫ f).app n ⟨⟨x, hx⟩, t⟩ := rfl

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. The restriction to A⊗Δ[1] of J on its 12 face is pr_A≫A.ι≫f. -/
private lemma symmHornMap_ι₁₂_restrict {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    (A : SSet.{u}) ◁ SSet.horn₂₂.ι₁₂ ≫
        (A.ι ▷ (SSet.horn 2 (2 : Fin 3) : SSet.{u})) ≫ symmHornMap H =
      fst _ _ ≫ A.ι ≫ f := by
  calc (A : SSet.{u}) ◁ SSet.horn₂₂.ι₁₂ ≫
          (A.ι ▷ (SSet.horn 2 (2 : Fin 3) : SSet.{u})) ≫ symmHornMap H
      = ((A : SSet.{u}) ◁ SSet.horn₂₂.ι₁₂ ≫
            A.ι ▷ (SSet.horn 2 (2 : Fin 3) : SSet.{u})) ≫ symmHornMap H := by
        simp only [Category.assoc]
    _ = ((A.ι ▷ (Δ[1] : SSet.{u})) ≫ X ◁ SSet.horn₂₂.ι₁₂) ≫ symmHornMap H := by
        rw [whisker_exchange]
    _ = A.ι ▷ (Δ[1] : SSet.{u}) ≫ (X ◁ SSet.horn₂₂.ι₁₂ ≫ symmHornMap H) := by
        simp only [Category.assoc]
    _ = A.ι ▷ (Δ[1] : SSet.{u}) ≫ H.h := by
        rw [symmHornMap_ι₁₂]
    _ = fst _ _ ≫ A.ι ≫ f := symmHornH_stationary H

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. On A⊗Δ[1], the 12 restriction of J equals the 12 restriction of
R=pr_A≫A.ι≫f. -/
private lemma symmHornMap_ι₁₂_stationaryAgree {X Y S : SSet.{u}}
    {p : Y ⟶ S} {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    (A : SSet.{u}) ◁ SSet.horn₂₂.ι₁₂ ≫
        (A.ι ▷ (SSet.horn 2 (2 : Fin 3) : SSet.{u})) ≫ symmHornMap H =
      (A : SSet.{u}) ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫
        symmStationaryFace f A := by
  rw [symmHornMap_ι₁₂_restrict H, symmStationaryFace_ι₁₂]

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. On A⊗Λ²₂, (A.ι⊗id)≫J=(id_A⊗horn.ι)≫R, where J:X⊗Λ²₂→Y and
R=pr_A≫A.ι≫f:A⊗Δ[2]→Y. -/
private lemma symmHornMap_commonIntersection {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    (A.ι ▷ (SSet.horn 2 (2 : Fin 3) : SSet.{u})) ≫ symmHornMap H =
    (A : SSet.{u}) ◁ (SSet.horn 2 (2 : Fin 3)).ι ≫
      symmStationaryFace f A := by
  apply (horn₂₂TensorLeftIsPushout (A : SSet.{u})).hom_ext
  · calc (A : SSet.{u}) ◁ SSet.horn₂₂.ι₀₂ ≫
          (A.ι ▷ (SSet.horn 2 (2 : Fin 3) : SSet.{u})) ≫ symmHornMap H
        = (A : SSet.{u}) ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫
            symmStationaryFace f A :=
          symmHornMap_ι₀₂_stationaryAgree H
      _ = (A : SSet.{u}) ◁ (SSet.horn₂₂.ι₀₂ ≫
            (SSet.horn 2 (2 : Fin 3)).ι) ≫
            symmStationaryFace f A := by
          rw [← SSet.horn.ι_ι (2 : Fin 3) (1 : Fin 3) (by decide)]
      _ = ((A : SSet.{u}) ◁ SSet.horn₂₂.ι₀₂ ≫
            (A : SSet.{u}) ◁ (SSet.horn 2 (2 : Fin 3)).ι) ≫
            symmStationaryFace f A := by
          rw [MonoidalCategory.whiskerLeft_comp]
      _ = (A : SSet.{u}) ◁ SSet.horn₂₂.ι₀₂ ≫
            (A : SSet.{u}) ◁ (SSet.horn 2 (2 : Fin 3)).ι ≫
              symmStationaryFace f A := by
          rw [Category.assoc]
  · calc (A : SSet.{u}) ◁ SSet.horn₂₂.ι₁₂ ≫
          (A.ι ▷ (SSet.horn 2 (2 : Fin 3) : SSet.{u})) ≫ symmHornMap H
        = (A : SSet.{u}) ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫
            symmStationaryFace f A :=
          symmHornMap_ι₁₂_stationaryAgree H
      _ = (A : SSet.{u}) ◁ (SSet.horn₂₂.ι₁₂ ≫
            (SSet.horn 2 (2 : Fin 3)).ι) ≫
            symmStationaryFace f A := by
          rw [← SSet.horn.ι_ι (2 : Fin 3) (0 : Fin 3) (by decide)]
      _ = ((A : SSet.{u}) ◁ SSet.horn₂₂.ι₁₂ ≫
            (A : SSet.{u}) ◁ (SSet.horn 2 (2 : Fin 3)).ι) ≫
            symmStationaryFace f A := by
          rw [MonoidalCategory.whiskerLeft_comp]
      _ = (A : SSet.{u}) ◁ SSet.horn₂₂.ι₁₂ ≫
            (A : SSet.{u}) ◁ (SSet.horn 2 (2 : Fin 3)).ι ≫
              symmStationaryFace f A := by
          rw [Category.assoc]

/-!
## The glued relative symmetry map

The horn and stationary maps glue to Φ:U₂→Y. Its two union restrictions are the outer-horn map
and the stationary map on A⊗Δ[2].
-/

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. The compatible maps J and R glue to Φ:U₂→Y, where U₂=(X⊗Λ²₂)∪(A⊗Δ[2]) is a
subcomplex of X⊗Δ[2]. -/
private noncomputable def symmUnionMap {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    (A.unionProd (SSet.horn 2 (2 : Fin 3)) : SSet.{u}) ⟶ Y :=
  (Subcomplex.unionProd.isPushout A (SSet.horn 2 (2 : Fin 3))).desc
    (symmHornMap H) (symmStationaryFace f A)
    (symmHornMap_commonIntersection H)

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. The first union inclusion X⊗Λ²₂→U₂ followed by Φ equals J. -/
private lemma symmUnionMap_ι₁ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫ symmUnionMap H =
      symmHornMap H :=
  (Subcomplex.unionProd.isPushout A (SSet.horn 2 (2 : Fin 3))).inl_desc _ _ _

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. The second union inclusion A⊗Δ[2]→U₂ followed by Φ equals R=pr_A≫A.ι≫f. -/
private lemma symmUnionMap_ι₂ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    Subcomplex.unionProd.ι₂ A (SSet.horn 2 (2 : Fin 3)) ≫ symmUnionMap H =
      symmStationaryFace f A :=
  (Subcomplex.unionProd.isPushout A (SSet.horn 2 (2 : Fin 3))).inr_desc _ _ _

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. C_g≫p=pr_X≫f≫p because f≫p=g≫p. -/
private lemma symmHornConst_over {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    symmHornConst g ≫ p = fst (X : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (f ≫ p) := by
  calc symmHornConst g ≫ p
      = (fst _ _ ≫ g) ≫ p := rfl
    _ = fst _ _ ≫ (g ≫ p) := by rw [Category.assoc]
    _ = fst _ _ ≫ (f ≫ p) := by rw [← H.map_eq]

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. J≫p=(id_X⊗horn.ι)≫Q, where Q=pr_X≫f≫p:X⊗Δ[2]→S. -/
private lemma symmHornMap_over {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    symmHornMap H ≫ p =
      (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) ≫ symmBaseMap p f := by
  apply (horn₂₂TensorLeftIsPushout X).hom_ext
  · have hL : (X ◁ SSet.horn₂₂.ι₀₂) ≫ symmHornMap H ≫ p =
        fst (X : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (f ≫ p) := by
      calc (X ◁ SSet.horn₂₂.ι₀₂) ≫ symmHornMap H ≫ p
          = ((X ◁ SSet.horn₂₂.ι₀₂) ≫ symmHornMap H) ≫ p := by
            rw [Category.assoc]
        _ = symmHornConst g ≫ p := by rw [symmHornMap_ι₀₂]
        _ = fst _ _ ≫ (f ≫ p) := symmHornConst_over H
    have hR : (X ◁ SSet.horn₂₂.ι₀₂) ≫
          (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) ≫ symmBaseMap p f =
        fst (X : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (f ≫ p) := by
      calc (X ◁ SSet.horn₂₂.ι₀₂) ≫
              (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) ≫ symmBaseMap p f
          = ((X ◁ SSet.horn₂₂.ι₀₂) ≫
                X ◁ (SSet.horn 2 (2 : Fin 3)).ι) ≫ symmBaseMap p f := by
            rw [Category.assoc]
        _ = (X ◁ (SSet.horn₂₂.ι₀₂ ≫ (SSet.horn 2 (2 : Fin 3)).ι)) ≫
              symmBaseMap p f := by
            rw [← MonoidalCategory.whiskerLeft_comp]
        _ = (X ◁ stdSimplex.δ (1 : Fin 3)) ≫ symmBaseMap p f := by
            rw [SSet.horn.ι_ι (2 : Fin 3) (1 : Fin 3) (by decide)]
        _ = (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫
              (fst _ _ ≫ (f ≫ p)) := by
            simp only [symmBaseMap]
        _ = ((X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫
              fst _ _) ≫ (f ≫ p) := by rw [← Category.assoc]
        _ = fst _ _ ≫ (f ≫ p) := by rw [whiskerLeft_fst]
    exact hL.trans hR.symm
  · have hL : (X ◁ SSet.horn₂₂.ι₁₂) ≫ symmHornMap H ≫ p =
        fst (X : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (f ≫ p) := by
      calc (X ◁ SSet.horn₂₂.ι₁₂) ≫ symmHornMap H ≫ p
          = ((X ◁ SSet.horn₂₂.ι₁₂) ≫ symmHornMap H) ≫ p := by
            rw [Category.assoc]
        _ = H.h ≫ p := by rw [symmHornMap_ι₁₂]
        _ = fst _ _ ≫ (f ≫ p) := H.over
    have hR : (X ◁ SSet.horn₂₂.ι₁₂) ≫
          (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) ≫ symmBaseMap p f =
        fst (X : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (f ≫ p) := by
      calc (X ◁ SSet.horn₂₂.ι₁₂) ≫
              (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) ≫ symmBaseMap p f
          = ((X ◁ SSet.horn₂₂.ι₁₂) ≫
                X ◁ (SSet.horn 2 (2 : Fin 3)).ι) ≫ symmBaseMap p f := by
            rw [Category.assoc]
        _ = (X ◁ (SSet.horn₂₂.ι₁₂ ≫ (SSet.horn 2 (2 : Fin 3)).ι)) ≫
              symmBaseMap p f := by
            rw [← MonoidalCategory.whiskerLeft_comp]
        _ = (X ◁ stdSimplex.δ (0 : Fin 3)) ≫ symmBaseMap p f := by
            rw [SSet.horn.ι_ι (2 : Fin 3) (0 : Fin 3) (by decide)]
        _ = (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫
              (fst _ _ ≫ (f ≫ p)) := by
            simp only [symmBaseMap]
        _ = ((X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫
              fst _ _) ≫ (f ≫ p) := by rw [← Category.assoc]
        _ = fst _ _ ≫ (f ≫ p) := by rw [whiskerLeft_fst]
    exact hL.trans hR.symm

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. With i:U₂→X⊗Δ[2], Φ≫p=i≫Q, where Q=pr_X≫f≫p. -/
private lemma symmUnionMap_over {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    symmUnionMap H ≫ p =
      (A.unionProd (SSet.horn 2 (2 : Fin 3))).ι ≫ symmBaseMap p f := by
  apply (Subcomplex.unionProd.isPushout A (SSet.horn 2 (2 : Fin 3))).hom_ext
  · calc Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫
              symmUnionMap H ≫ p
          = (Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫
              symmUnionMap H) ≫ p := by rw [Category.assoc]
        _ = symmHornMap H ≫ p := by rw [symmUnionMap_ι₁]
        _ = (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) ≫ symmBaseMap p f := by
            rw [symmHornMap_over H]
        _ = Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫
              (A.unionProd (SSet.horn 2 (2 : Fin 3))).ι ≫
                symmBaseMap p f := by
            rw [Subcomplex.unionProd.ι₁_ι_assoc]
  · calc Subcomplex.unionProd.ι₂ A (SSet.horn 2 (2 : Fin 3)) ≫
              symmUnionMap H ≫ p
          = (Subcomplex.unionProd.ι₂ A (SSet.horn 2 (2 : Fin 3)) ≫
              symmUnionMap H) ≫ p := by rw [Category.assoc]
        _ = symmStationaryFace f A ≫ p := by rw [symmUnionMap_ι₂]
        _ = (A.ι ▷ (Δ[2] : SSet.{u})) ≫ symmBaseMap p f := by
            rw [symmStationaryFace_over]
        _ = Subcomplex.unionProd.ι₂ A (SSet.horn 2 (2 : Fin 3)) ≫
              (A.unionProd (SSet.horn 2 (2 : Fin 3))).ι ≫
                symmBaseMap p f := by
            rw [Subcomplex.unionProd.ι₂_ι_assoc]

/-!
## The symmetry lifting square

The inclusion U₂→X⊗Δ[2], map Φ:U₂→Y, fibration p:Y→S and base map Q=pr_X≫f≫p form the square
Φ≫p=i≫Q.
-/

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. The maps Φ:U₂→Y, i:U₂→X⊗Δ[2], p:Y→S and Q=pr_X≫f≫p form the commuting
square Φ≫p=i≫Q. -/
private theorem symmUnionCommSq {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    CommSq (symmUnionMap H)
      (A.unionProd (SSet.horn 2 (2 : Fin 3))).ι
      p (symmBaseMap p f) :=
  CommSq.mk (symmUnionMap_over H)

/-- For X in universe u and A⊆X, the inclusion (X⊗Λ²₂)∪(A⊗Δ[2])→X⊗Δ[2] is an anodyne extension. -/
private lemma symmUnionProd_horn_ι_mem_anodyneExtensions
    {X : SSet.{u}} (A : X.Subcomplex) :
    SSet.anodyneExtensions
      (A.unionProd (SSet.horn 2 (2 : Fin 3))).ι := by
  have hHorn : SSet.anodyneExtensions (SSet.horn 2 (2 : Fin 3)).ι :=
    SSet.anodyneExtensions.horn_ι (2 : Fin 3)
  exact SSet.anodyneExtensions_unionProd_ι A (SSet.horn 2 (2 : Fin 3)) hHorn

/-!
## The selected symmetry filler

The relative outer-horn union inclusion is anodyne. A simplicial fibration p therefore supplies
F₂:X⊗Δ[2]→Y extending Φ and lying over Q.
-/

private lemma symmUnionProd_horn_ι_hasLiftingProperty
    {X : SSet.{u}} (A : X.Subcomplex)
    {Y S : SSet.{u}} {p : Y ⟶ S} [Fibration p] :
    HasLiftingProperty (A.unionProd (SSet.horn 2 (2 : Fin 3))).ι p :=
  (symmUnionProd_horn_ι_mem_anodyneExtensions A) p
    (by rwa [← HomotopicalAlgebra.fibration_iff])

private instance symmUnionProd_horn_hasLiftingPropertyInst
    {X : SSet.{u}} {A : X.Subcomplex}
    {Y S : SSet.{u}} {p : Y ⟶ S} [Fibration p] :
    HasLiftingProperty (A.unionProd (SSet.horn 2 (2 : Fin 3))).ι p :=
  symmUnionProd_horn_ι_hasLiftingProperty A

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. If p is a simplicial fibration, the relative outer-horn lifting square
selects F₂:X⊗Δ[2]→Y extending Φ:U₂→Y and lying over Q=pr_X≫f≫p. -/
private noncomputable def symmFiller {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H : HomotopyRelOver p f g A) :
    X ⊗ (Δ[2] : SSet.{u}) ⟶ Y :=
  (symmUnionCommSq H).lift

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. For p a simplicial fibration, F₂≫p=Q=pr_X≫f≫p. -/
private lemma symmFiller_over {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H : HomotopyRelOver p f g A) :
    symmFiller H ≫ p = symmBaseMap p f :=
  (symmUnionCommSq H).fac_right

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. For p a simplicial fibration and i:U₂→X⊗Δ[2], i≫F₂=Φ. -/
private lemma symmFiller_union {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H : HomotopyRelOver p f g A) :
    (A.unionProd (SSet.horn 2 (2 : Fin 3))).ι ≫ symmFiller H = symmUnionMap H :=
  (symmUnionCommSq H).fac_left

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. For p a simplicial fibration, define G=(id_X⊗δ₂)≫F₂:X⊗Δ[1]→Y. The missing
01 edge of the outer horn is the reverse homotopy g≃f. -/
private noncomputable def symmHomotopy {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H : HomotopyRelOver p f g A) :
    X ⊗ (Δ[1] : SSet.{u}) ⟶ Y :=
  (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ symmFiller H

/-!
## The initial vertex of the reversed edge

The missing edge δ₂ and the specified constant edge δ₁ both send interval vertex 0 to
two-simplex vertex 0. Their restrictions show that the reversed cylinder begins at g.
-/

/-- For the outer horn Λ²₂⊆Δ[2] in universe u, δ₁:Δ[1]→Δ[2] equals the 02 face inclusion into the
horn followed by horn.ι. -/
private lemma symm_delta₁_eq :
    (stdSimplex.δ (1 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) =
      SSet.horn₂₂.ι₀₂ ≫ (SSet.horn 2 (2 : Fin 3)).ι := by
  rw [← SSet.horn.ι_ι (2 : Fin 3) (1 : Fin 3) (by decide)]

/-- For X in universe u, id_X⊗δ₁ is the composite X⊗Δ[1]→X⊗Λ²₂→X⊗Δ[2] through the horn's 02 edge. -/
private lemma symm_whisker_δ₁ {X : SSet.{u}} :
    (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) =
      (X ◁ SSet.horn₂₂.ι₀₂) ≫ (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) := by
  calc (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]))
      = X ◁ (SSet.horn₂₂.ι₀₂ ≫ (SSet.horn 2 (2 : Fin 3)).ι) := by
        rw [symm_delta₁_eq]
    _ = (X ◁ SSet.horn₂₂.ι₀₂) ≫ (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) := by
        rw [MonoidalCategory.whiskerLeft_comp]

/-- For g:X→Y in universe u and C_g=pr_X≫g, its source endpoint satisfies ι₀≫C_g=g. -/
private lemma symmHornConst_ι₀ {X Y : SSet.{u}} (g : X ⟶ Y) :
    SSet.ι₀ ≫ (symmHornConst g : X ⊗ Δ[1] ⟶ Y) = g := by
  calc SSet.ι₀ ≫ (symmHornConst g : X ⊗ Δ[1] ⟶ Y)
      = SSet.ι₀ ≫ (fst _ _ ≫ g) := rfl
    _ = (SSet.ι₀ ≫ fst _ _) ≫ g := by rw [Category.assoc]
    _ = g := by rw [SSet.ι₀_fst, Category.id_comp]

/-- In universe u, the coface δ₁:Δ[1]→Δ[2] sends geometric vertex 0 to vertex 0. -/
private lemma symm_δ₁_zero :
    (stdSimplex.δ (1 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]).app _
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2) : (Δ[1] : SSet.{u}) _⦋0⦌) =
      stdSimplex.obj₀Equiv.symm (0 : Fin 3) := rfl

private lemma symm_δ₂_zero :
    (stdSimplex.δ (2 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]).app _
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2) : (Δ[1] : SSet.{u}) _⦋0⦌) =
      stdSimplex.obj₀Equiv.symm (0 : Fin 3) := rfl

/-- For X in universe u, ι₀≫(id_X⊗δ₁)=ι₀≫(id_X⊗δ₂):X→X⊗Δ[2], since both cofaces send vertex 0 to
vertex 0. -/
private lemma symm_iota₀_δ₁_eq_δ₂ {X : SSet.{u}} :
    SSet.ι₀ ≫ (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) =
      SSet.ι₀ ≫ (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) := by
  -- `ι₀ = lift (𝟙 X) (const 0)` and `lift _ _ ≫ X ◁ δ = lift _ (const 0 ≫ δ)`
  calc SSet.ι₀ (X := X) ≫ (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]))
      = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≫
            (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) := by
        rw [← CartesianMonoidalCategory.lift_whiskerLeft]
        rfl
    _ = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const
            ((stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]).app _
              (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) := by
        rw [SSet.const_comp]
    _ = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 3) : (Δ[2] : SSet.{u}) _⦋0⦌)) := by
        rw [symm_δ₁_zero]
    _ = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const
            ((stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]).app _
              (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) := by
        rw [symm_δ₂_zero]
    _ = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≫
            (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) := by
        rw [SSet.const_comp]
    _ = SSet.ι₀ (X := X) ≫ (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) := by
        rw [← CartesianMonoidalCategory.lift_whiskerLeft]
        rfl

/-- For X in universe u and A⊆X, X⊗Λ²₂→X⊗Δ[2] is the first union inclusion X⊗Λ²₂→U₂ followed by
U₂→X⊗Δ[2]. -/
private lemma symm_horn_whisker_eq_unionProd {X : SSet.{u}}
    (A : X.Subcomplex) :
    (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) =
      Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫
        (A.unionProd (SSet.horn 2 (2 : Fin 3))).ι := by
  rw [← Subcomplex.unionProd.ι₁_ι]

private lemma symmHomotopy_ι₀ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H : HomotopyRelOver p f g A) :
    SSet.ι₀ ≫ symmHomotopy H = g := by
  calc SSet.ι₀ ≫ symmHomotopy H
      = SSet.ι₀ ≫ (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ symmFiller H := rfl
    _ = SSet.ι₀ ≫ (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ symmFiller H := by
        rw [← Category.assoc, ← Category.assoc, symm_iota₀_δ₁_eq_δ₂]
    _ = (SSet.ι₀ ≫ (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]))) ≫ symmFiller H := by
        rw [Category.assoc]
    _ = (SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₀₂) ≫ (X ◁ (SSet.horn 2 (2 : Fin 3)).ι)) ≫
        symmFiller H := by
        rw [symm_whisker_δ₁]
    _ = (SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₀₂)) ≫
        (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) ≫ symmFiller H := by
        simp only [Category.assoc]
    _ = (SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₀₂)) ≫
        (Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫
          (A.unionProd (SSet.horn 2 (2 : Fin 3))).ι) ≫ symmFiller H := by
        rw [symm_horn_whisker_eq_unionProd A]
    _ = (SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₀₂)) ≫
        Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫
          ((A.unionProd (SSet.horn 2 (2 : Fin 3))).ι ≫ symmFiller H) := by
        simp only [Category.assoc]
    _ = (SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₀₂)) ≫
        Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫
          symmUnionMap H := by
        rw [symmFiller_union H]
    _ = (SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₀₂)) ≫
        (Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫ symmUnionMap H) := by
        rw [Category.assoc]
    _ = (SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₀₂)) ≫ symmHornMap H := by
        rw [symmUnionMap_ι₁]
    _ = SSet.ι₀ ≫ ((X ◁ SSet.horn₂₂.ι₀₂) ≫ symmHornMap H) := by
        rw [Category.assoc]
    _ = SSet.ι₀ ≫ (symmHornConst g : X ⊗ (Δ[1] : SSet.{u}) ⟶ Y) := by
        rw [symmHornMap_ι₀₂]
    _ = g := by
        rw [symmHornConst_ι₀]

/-!
## The final vertex of the reversed edge

The missing edge δ₂ sends interval vertex 1 to two-simplex vertex 1, also reached by vertex 0 of
the specified δ₀ face H. Thus the reversed cylinder ends at f.
-/

/-- For Λ²₂⊆Δ[2] in universe u, δ₀:Δ[1]→Δ[2] equals the 12 edge inclusion into the horn followed by
horn.ι. -/
private lemma symm_delta₀_eq :
    (stdSimplex.δ (0 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) =
      SSet.horn₂₂.ι₁₂ ≫ (SSet.horn 2 (2 : Fin 3)).ι := by
  rw [← SSet.horn.ι_ι (2 : Fin 3) (0 : Fin 3) (by decide)]

/-- For X in universe u, id_X⊗δ₀ is the composite X⊗Δ[1]→X⊗Λ²₂→X⊗Δ[2] through the horn's 12 edge. -/
private lemma symm_whisker_δ₀ {X : SSet.{u}} :
    (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) =
      (X ◁ SSet.horn₂₂.ι₁₂) ≫ (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) := by
  calc (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2]))
      = X ◁ (SSet.horn₂₂.ι₁₂ ≫ (SSet.horn 2 (2 : Fin 3)).ι) := by
        rw [symm_delta₀_eq]
    _ = (X ◁ SSet.horn₂₂.ι₁₂) ≫ (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) := by
        rw [MonoidalCategory.whiskerLeft_comp]

/-- In universe u, δ₀:Δ[1]→Δ[2] sends geometric vertex 0 to vertex 1. -/
private lemma symm_δ₀_zero :
    (stdSimplex.δ (0 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]).app _
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2) : (Δ[1] : SSet.{u}) _⦋0⦌) =
      stdSimplex.obj₀Equiv.symm (1 : Fin 3) := rfl

/-- In universe u, δ₂:Δ[1]→Δ[2] sends geometric vertex 1 to vertex 1. -/
private lemma symm_δ₂_one :
    (stdSimplex.δ (2 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]).app _
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2) : (Δ[1] : SSet.{u}) _⦋0⦌) =
      stdSimplex.obj₀Equiv.symm (1 : Fin 3) := rfl

/-- For X in universe u, ι₁≫(id_X⊗δ₂)=ι₀≫(id_X⊗δ₀):X→X⊗Δ[2], since both composites have
second-coordinate vertex 1. -/
private lemma symm_iota₁_δ₂_eq_ι₀_δ₀ {X : SSet.{u}} :
    SSet.ι₁ ≫ (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) =
      SSet.ι₀ ≫ (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) := by
  calc SSet.ι₁ (X := X) ≫ (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]))
      = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ≫
            (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) := by
        rw [← CartesianMonoidalCategory.lift_whiskerLeft]
        rfl
    _ = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const
            ((stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]).app _
              (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) := by
        rw [SSet.const_comp]
    _ = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 3) : (Δ[2] : SSet.{u}) _⦋0⦌)) := by
        rw [symm_δ₂_one]
    _ = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const
            ((stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2]).app _
              (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) := by
        rw [symm_δ₀_zero]
    _ = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≫
            (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) := by
        rw [SSet.const_comp]
    _ = SSet.ι₀ (X := X) ≫ (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) := by
        rw [← CartesianMonoidalCategory.lift_whiskerLeft]
        rfl

private lemma symmHomotopy_ι₁ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H : HomotopyRelOver p f g A) :
    SSet.ι₁ ≫ symmHomotopy H = f := by
  calc SSet.ι₁ ≫ symmHomotopy H
      = SSet.ι₁ ≫ (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ symmFiller H := rfl
    _ = (SSet.ι₁ ≫ (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]))) ≫ symmFiller H := by
        rw [Category.assoc]
    _ = (SSet.ι₀ ≫ (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2]))) ≫ symmFiller H := by
        rw [symm_iota₁_δ₂_eq_ι₀_δ₀]
    _ = SSet.ι₀ ≫ (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ symmFiller H := by
        rw [Category.assoc]
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₁₂ ≫ (X ◁ (SSet.horn 2 (2 : Fin 3)).ι)) ≫
        symmFiller H := by
        rw [symm_whisker_δ₀]
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₁₂) ≫
        (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) ≫ symmFiller H := by
        simp only [Category.assoc]
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₁₂) ≫
        (Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫
          (A.unionProd (SSet.horn 2 (2 : Fin 3))).ι) ≫ symmFiller H := by
        rw [symm_horn_whisker_eq_unionProd A]
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₁₂) ≫
        Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫
          ((A.unionProd (SSet.horn 2 (2 : Fin 3))).ι ≫ symmFiller H) := by
        simp only [Category.assoc]
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₁₂) ≫
        Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫
          symmUnionMap H := by
        rw [symmFiller_union H]
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₁₂) ≫
        (Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫ symmUnionMap H) := rfl
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₁₂) ≫ symmHornMap H := by
        rw [symmUnionMap_ι₁]
    _ = SSet.ι₀ ≫ ((X ◁ SSet.horn₂₂.ι₁₂) ≫ symmHornMap H) := rfl
    _ = SSet.ι₀ ≫ H.h := by
        rw [symmHornMap_ι₁₂]
    _ = f := by
        rw [H.h₀]

/-!
## Relative and base conditions for the reversed edge

The symmetry filler restricts on A⊗Δ[2] to the stationary f-map. Equality of f and g on A makes
the reversed edge stationary at g; its base projection is pr_X≫g≫p.
-/

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. For p a simplicial fibration, restricting F₂ to A⊗Δ[2] gives R=pr_A≫A.ι≫f. -/
private lemma symmFiller_restrict {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H : HomotopyRelOver p f g A) :
    (A.ι ▷ (Δ[2] : SSet.{u})) ≫ symmFiller H = symmStationaryFace f A := by
  calc (A.ι ▷ (Δ[2] : SSet.{u})) ≫ symmFiller H
      = (Subcomplex.unionProd.ι₂ A (SSet.horn 2 (2 : Fin 3)) ≫
          (A.unionProd (SSet.horn 2 (2 : Fin 3))).ι) ≫ symmFiller H := by
        rw [← Subcomplex.unionProd.ι₂_ι]
    _ = Subcomplex.unionProd.ι₂ A (SSet.horn 2 (2 : Fin 3)) ≫
          ((A.unionProd (SSet.horn 2 (2 : Fin 3))).ι ≫ symmFiller H) := by
        rw [Category.assoc]
    _ = Subcomplex.unionProd.ι₂ A (SSet.horn 2 (2 : Fin 3)) ≫ symmUnionMap H := by
        rw [symmFiller_union H]
    _ = symmStationaryFace f A := by
        rw [symmUnionMap_ι₂ H]

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. For p a simplicial fibration, G=(id_X⊗δ₂)≫F₂ satisfies G_c(a,t)=g_c(a) for
every simplex a∈A_c and t∈Δ[1]_c. -/
private lemma symmHomotopy_stationary {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H : HomotopyRelOver p f g A) {n : SimplexCategoryᵒᵖ}
    {x : X.obj n} (hx : x ∈ A.obj n) (t : (Δ[1] : SSet.{u}).obj n) :
    (symmHomotopy H).app n ⟨x, t⟩ = g.app n x := by
  have h_whisker_δ₂ : (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])).app n ⟨x, t⟩ =
      ⟨x, (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ := rfl
  have h_filler : (symmFiller H).app n
      ⟨x, (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ = f.app n x := by
    have hA : (A.ι ▷ (Δ[2] : SSet.{u})).app n
        ⟨⟨x, hx⟩, (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ =
        ⟨x, (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ := rfl
    calc (symmFiller H).app n
          ⟨x, (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩
        = (symmFiller H).app n
            ((A.ι ▷ (Δ[2] : SSet.{u})).app n
              ⟨⟨x, hx⟩, (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩) := by
          rw [hA]
      _ = ((A.ι ▷ (Δ[2] : SSet.{u})) ≫ symmFiller H).app n
            ⟨⟨x, hx⟩, (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ := rfl
      _ = (symmStationaryFace f A).app n
            ⟨⟨x, hx⟩, (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ := by
          rw [symmFiller_restrict H]
      _ = f.app n x := rfl
  have h_eq_f : (symmHomotopy H).app n ⟨x, t⟩ = f.app n x := by
    calc (symmHomotopy H).app n ⟨x, t⟩
        = ((X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ symmFiller H).app n ⟨x, t⟩ := rfl
      _ = (symmFiller H).app n
            ((X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])).app n ⟨x, t⟩) := rfl
      _ = (symmFiller H).app n
            ⟨x, (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ := by
          rw [h_whisker_δ₂]
      _ = f.app n x := h_filler
  have h_fg : f.app n x = g.app n x := by
    calc f.app n x
        = (A.ι ≫ f).app n ⟨x, hx⟩ := rfl
      _ = (A.ι ≫ g).app n ⟨x, hx⟩ := by
          rw [stationary_ends H]
      _ = g.app n x := rfl
  exact h_eq_f.trans h_fg

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. For p a simplicial fibration, G≫p=pr_X≫g≫p:X⊗Δ[1]→S. -/
private lemma symmHomotopy_over {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H : HomotopyRelOver p f g A) :
    symmHomotopy H ≫ p = fst _ _ ≫ (g ≫ p) := by
  calc symmHomotopy H ≫ p
      = (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫ symmFiller H) ≫ p := rfl
    _ = (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ (symmFiller H ≫ p) := by
        rw [Category.assoc]
    _ = (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ symmBaseMap p f := by
        rw [symmFiller_over H]
    _ = (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫
          (fst X _ ≫ (f ≫ p)) := by
        simp only [symmBaseMap]
    _ = ((X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ fst X _) ≫ (f ≫ p) := by
        rw [Category.assoc]
    _ = fst _ _ ≫ (f ≫ p) := by
        rw [whiskerLeft_fst]
    _ = fst _ _ ≫ (g ≫ p) := by
        rw [← H.map_eq]

/-- For X,Y,S in simplicial-set universe u, p:Y→S, f,g:X→Y and A⊆X, let H:f≃g be stationary on A and
satisfy H≫p=pr_X≫f≫p. If p is a simplicial fibration, the outer-horn construction gives a
reverse homotopy g≃f, stationary on A, with base composite pr_X≫g≫p. -/
@[no_expose]
noncomputable def symm [Fibration p] (H : HomotopyRelOver p f g A) :
    HomotopyRelOver p g f A where
  toHomotopyRel :=
    { h := symmHomotopy H
      h₀ := symmHomotopy_ι₀ H
      h₁ := symmHomotopy_ι₁ H
      stationary := fun _ hx t => symmHomotopy_stationary H hx t }
  over := symmHomotopy_over H

/-!
## The inner horn for composition

For H₀₁:f≃g and H₁₂:g≃k, the 01 and 12 edges of Λ²₁ carry these two homotopies and agree at g.
The stationary map on A⊗Δ[2] agrees with both edge restrictions.
-/

/-- For X in universe u, the 01 and 12 edges of Λ²₁ meet at vertex 1. Tensoring their pushout
presentation with X gives the pushout presentation of X⊗Λ²₁. -/
private theorem horn₂₁TensorLeftIsPushout (X : SSet.{u}) :
    IsPushout
      (X ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1]))
      (X ◁ (stdSimplex.δ (1 : Fin 2) : Δ[0] ⟶ Δ[1]))
      (X ◁ SSet.horn₂₁.ι₀₁)
      (X ◁ SSet.horn₂₁.ι₁₂) := by
  have : PreservesColimit
      (span (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1])
        (stdSimplex.δ (1 : Fin 2) : Δ[0] ⟶ Δ[1]))
      (MonoidalCategory.tensorLeft (X : SSet.{u})) :=
    inferInstance
  exact (MonoidalCategory.tensorLeft (X : SSet.{u})).map_isPushout
    SSet.horn₂₁.isPushout

/-- For X,Y,S in universe u, p:Y→S, f,g,k:X→Y and A⊆X, let H₀₁:f≃g and H₁₂:g≃k be stationary on A
and over p. Restricting H₀₁ along id_X⊗δ₀ gives pr_X≫g:X⊗Δ[0]→Y. -/
private lemma transHornH₀₁_δ₀ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) :
    (X ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1])) ≫ H₀₁.h =
      fst _ _ ≫ g := by
  ext n ⟨x, t₀⟩
  have hδ : stdSimplex.δ (0 : Fin 2) =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
    stdSimplex.δ_zero_eq_const
  have h_pair :
      (X ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1])).app n ⟨x, t₀⟩ =
        SSet.ι₁.app n x := by
    have h₁ : (X ◁ (stdSimplex.δ (0 : Fin 2))).app n ⟨x, t₀⟩ =
        ⟨x, (stdSimplex.δ (0 : Fin 2)).app n t₀⟩ := rfl
    have h₂ : (stdSimplex.δ (0 : Fin 2)).app n t₀ =
        (SSet.const (stdSimplex.obj₀Equiv.symm 1) : X ⟶ Δ[1]).app n x := by
      rw [hδ]
      rfl
    have h₃ : SSet.ι₁.app n x =
        ⟨x, (SSet.const (stdSimplex.obj₀Equiv.symm 1) : X ⟶ Δ[1]).app n x⟩ := rfl
    rw [h₁, h₂, ← h₃]
  calc H₀₁.h.app n ((X ◁ (stdSimplex.δ (0 : Fin 2))).app n ⟨x, t₀⟩)
      = H₀₁.h.app n (SSet.ι₁.app n x) := by rw [h_pair]
    _ = (SSet.ι₁ ≫ H₀₁.h).app n x := rfl
    _ = g.app n x := by rw [H₀₁.h₁]
    _ = (fst _ _ ≫ g).app n ⟨x, t₀⟩ := rfl

/-- For X,Y,S in universe u, p:Y→S, f,g,k:X→Y and A⊆X, let H₀₁:f≃g and H₁₂:g≃k be stationary on A
and over p. Restricting H₁₂ along id_X⊗δ₁ gives pr_X≫g:X⊗Δ[0]→Y. -/
private lemma transHornH₁₂_δ₁ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {g h : X ⟶ Y} {A : X.Subcomplex}
    (H₁₂ : HomotopyRelOver p g h A) :
    (X ◁ (stdSimplex.δ (1 : Fin 2) : Δ[0] ⟶ Δ[1])) ≫ H₁₂.h =
      fst _ _ ≫ g := by
  ext n ⟨x, t₀⟩
  have hδ : stdSimplex.δ (1 : Fin 2) =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :=
    stdSimplex.δ_one_eq_const
  have h_pair :
      (X ◁ (stdSimplex.δ (1 : Fin 2) : Δ[0] ⟶ Δ[1])).app n ⟨x, t₀⟩ =
        SSet.ι₀.app n x := by
    have h₁ : (X ◁ (stdSimplex.δ (1 : Fin 2))).app n ⟨x, t₀⟩ =
        ⟨x, (stdSimplex.δ (1 : Fin 2)).app n t₀⟩ := rfl
    have h₂ : (stdSimplex.δ (1 : Fin 2)).app n t₀ =
        (SSet.const (stdSimplex.obj₀Equiv.symm 0) : X ⟶ Δ[1]).app n x := by
      rw [hδ]
      rfl
    have h₃ : SSet.ι₀.app n x =
        ⟨x, (SSet.const (stdSimplex.obj₀Equiv.symm 0) : X ⟶ Δ[1]).app n x⟩ := rfl
    rw [h₁, h₂, ← h₃]
  calc H₁₂.h.app n ((X ◁ (stdSimplex.δ (1 : Fin 2))).app n ⟨x, t₀⟩)
      = H₁₂.h.app n (SSet.ι₀.app n x) := by rw [h_pair]
    _ = (SSet.ι₀ ≫ H₁₂.h).app n x := rfl
    _ = g.app n x := by rw [H₁₂.h₀]
    _ = (fst _ _ ≫ g).app n ⟨x, t₀⟩ := rfl

/-- For X,Y,S in universe u, p:Y→S, f,g,k:X→Y and A⊆X, let H₀₁:f≃g and H₁₂:g≃k be stationary on A
and over p. The 01 face H₀₁ and 12 face H₁₂ agree at vertex 1, giving g. -/
private lemma transHornFaces_agree {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    (X ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1])) ≫ H₀₁.h =
      (X ◁ (stdSimplex.δ (1 : Fin 2) : Δ[0] ⟶ Δ[1])) ≫ H₁₂.h := by
  rw [transHornH₀₁_δ₀ H₀₁, transHornH₁₂_δ₁ H₁₂]

/-- For X,Y,S in universe u, p:Y→S, f,g,k:X→Y and A⊆X, let H₀₁:f≃g and H₁₂:g≃k be stationary on A
and over p. The two faces define J₁:X⊗Λ²₁→Y, with 01 edge H₀₁ and 12 edge H₁₂. -/
private noncomputable def transHornMap {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    X ⊗ (SSet.horn 2 (1 : Fin 3) : SSet.{u}) ⟶ Y :=
  (horn₂₁TensorLeftIsPushout X).desc
    H₀₁.h H₁₂.h (transHornFaces_agree H₀₁ H₁₂)

/-- For X,Y,S in universe u, p:Y→S, f,g,k:X→Y and A⊆X, let H₀₁:f≃g and H₁₂:g≃k be stationary on A
and over p. Restricting J₁ to the 01 edge gives H₀₁. -/
@[reassoc]
private lemma transHornMap_ι₀₁ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    (X ◁ SSet.horn₂₁.ι₀₁) ≫ transHornMap H₀₁ H₁₂ = H₀₁.h :=
  (horn₂₁TensorLeftIsPushout X).inl_desc _ _ _

/-- For X,Y,S in universe u, p:Y→S, f,g,k:X→Y and A⊆X, let H₀₁:f≃g and H₁₂:g≃k be stationary on A
and over p. Restricting J₁ to the 12 edge gives H₁₂. -/
@[reassoc]
private lemma transHornMap_ι₁₂ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    (X ◁ SSet.horn₂₁.ι₁₂) ≫ transHornMap H₀₁ H₁₂ = H₁₂.h :=
  (horn₂₁TensorLeftIsPushout X).inr_desc _ _ _

/-- For f:X→Y and A⊆X in universe u, R=pr_A≫A.ι≫f on A⊗Δ[2] restricts along the 01 edge to
pr_A≫A.ι≫f. -/
private lemma transStationaryFace_ι₀₁ {X Y : SSet.{u}} (f : X ⟶ Y)
    (A : X.Subcomplex) :
    (A : SSet.{u}) ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫
        symmStationaryFace f A =
      fst _ _ ≫ A.ι ≫ f := by
  calc (A : SSet.{u}) ◁ stdSimplex.δ (2 : Fin 3) ≫ symmStationaryFace f A
      = (A : SSet.{u}) ◁ stdSimplex.δ (2 : Fin 3) ≫
          (fst (A : SSet.{u}) (Δ[2] : SSet.{u}) ≫ A.ι ≫ f) := rfl
    _ = ((A : SSet.{u}) ◁ stdSimplex.δ (2 : Fin 3) ≫
          fst (A : SSet.{u}) (Δ[2] : SSet.{u})) ≫ A.ι ≫ f := by
        simp only [Category.assoc]
    _ = fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ f := by
        rw [whiskerLeft_fst]

/-- For X,Y,S in universe u, p:Y→S, f,g,k:X→Y and A⊆X, let H₀₁:f≃g and H₁₂:g≃k be stationary on A
and over p. The 01 restriction of J₁ to A⊗Δ[1] is pr_A≫A.ι≫f. -/
private lemma transHornMap_ι₀₁_restrict {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    (A : SSet.{u}) ◁ SSet.horn₂₁.ι₀₁ ≫
        (A.ι ▷ (SSet.horn 2 (1 : Fin 3) : SSet.{u})) ≫ transHornMap H₀₁ H₁₂ =
      fst _ _ ≫ A.ι ≫ f := by
  calc (A : SSet.{u}) ◁ SSet.horn₂₁.ι₀₁ ≫
          (A.ι ▷ (SSet.horn 2 (1 : Fin 3) : SSet.{u})) ≫ transHornMap H₀₁ H₁₂
      = ((A : SSet.{u}) ◁ SSet.horn₂₁.ι₀₁ ≫
            A.ι ▷ (SSet.horn 2 (1 : Fin 3) : SSet.{u})) ≫ transHornMap H₀₁ H₁₂ := by
        simp only [Category.assoc]
    _ = ((A.ι ▷ (Δ[1] : SSet.{u})) ≫ X ◁ SSet.horn₂₁.ι₀₁) ≫ transHornMap H₀₁ H₁₂ := by
        rw [whisker_exchange]
    _ = A.ι ▷ (Δ[1] : SSet.{u}) ≫ (X ◁ SSet.horn₂₁.ι₀₁ ≫ transHornMap H₀₁ H₁₂) := by
        simp only [Category.assoc]
    _ = A.ι ▷ (Δ[1] : SSet.{u}) ≫ H₀₁.h := by
        rw [transHornMap_ι₀₁]
    _ = fst _ _ ≫ A.ι ≫ f := symmHornH_stationary H₀₁

/-- For X,Y,S in universe u, p:Y→S, f,g,k:X→Y and A⊆X, let H₀₁:f≃g and H₁₂:g≃k be stationary on A
and over p. The 12 restriction of J₁ to A⊗Δ[1] equals pr_A≫A.ι≫f, since A.ι≫f=A.ι≫g. -/
private lemma transHornMap_ι₁₂_restrict {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    (A : SSet.{u}) ◁ SSet.horn₂₁.ι₁₂ ≫
        (A.ι ▷ (SSet.horn 2 (1 : Fin 3) : SSet.{u})) ≫ transHornMap H₀₁ H₁₂ =
      fst _ _ ≫ A.ι ≫ f := by
  calc (A : SSet.{u}) ◁ SSet.horn₂₁.ι₁₂ ≫
          (A.ι ▷ (SSet.horn 2 (1 : Fin 3) : SSet.{u})) ≫ transHornMap H₀₁ H₁₂
      = ((A : SSet.{u}) ◁ SSet.horn₂₁.ι₁₂ ≫
            A.ι ▷ (SSet.horn 2 (1 : Fin 3) : SSet.{u})) ≫ transHornMap H₀₁ H₁₂ := by
        simp only [Category.assoc]
    _ = ((A.ι ▷ (Δ[1] : SSet.{u})) ≫ X ◁ SSet.horn₂₁.ι₁₂) ≫ transHornMap H₀₁ H₁₂ := by
        rw [whisker_exchange]
    _ = A.ι ▷ (Δ[1] : SSet.{u}) ≫ (X ◁ SSet.horn₂₁.ι₁₂ ≫ transHornMap H₀₁ H₁₂) := by
        simp only [Category.assoc]
    _ = A.ι ▷ (Δ[1] : SSet.{u}) ≫ H₁₂.h := by
        rw [transHornMap_ι₁₂]
    _ = fst _ _ ≫ A.ι ≫ g := symmHornH_stationary H₁₂
    _ = fst _ _ ≫ A.ι ≫ f := by
        have hg : A.ι ≫ g = A.ι ≫ f := (stationary_ends H₀₁).symm
        calc fst _ _ ≫ A.ι ≫ g
            = fst _ _ ≫ (A.ι ≫ g) := rfl
          _ = fst _ _ ≫ (A.ι ≫ f) := by rw [hg]
          _ = fst _ _ ≫ A.ι ≫ f := rfl

/-- For X,Y,S in universe u, p:Y→S, f,g,k:X→Y and A⊆X, let H₀₁:f≃g and H₁₂:g≃k be stationary on A
and over p. The 01 restriction of J₁ on A agrees with the 01 restriction of R=pr_A≫A.ι≫f. -/
private lemma transHornMap_ι₀₁_stationaryAgree {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    (A : SSet.{u}) ◁ SSet.horn₂₁.ι₀₁ ≫
        (A.ι ▷ (SSet.horn 2 (1 : Fin 3) : SSet.{u})) ≫ transHornMap H₀₁ H₁₂ =
      (A : SSet.{u}) ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫
        symmStationaryFace f A := by
  rw [transHornMap_ι₀₁_restrict H₀₁ H₁₂, transStationaryFace_ι₀₁]

/-- For X,Y,S in universe u, p:Y→S, f,g,k:X→Y and A⊆X, let H₀₁:f≃g and H₁₂:g≃k be stationary on A
and over p. The 12 restriction of J₁ on A agrees with the 12 restriction of R=pr_A≫A.ι≫f. -/
private lemma transHornMap_ι₁₂_stationaryAgree {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    (A : SSet.{u}) ◁ SSet.horn₂₁.ι₁₂ ≫
        (A.ι ▷ (SSet.horn 2 (1 : Fin 3) : SSet.{u})) ≫ transHornMap H₀₁ H₁₂ =
      (A : SSet.{u}) ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫
        symmStationaryFace f A := by
  rw [transHornMap_ι₁₂_restrict H₀₁ H₁₂, symmStationaryFace_ι₁₂]

/-- For X,Y,S in universe u, p:Y→S, f,g,k:X→Y and A⊆X, let H₀₁:f≃g and H₁₂:g≃k be stationary on A
and over p. On A⊗Λ²₁, (A.ι⊗id)≫J₁=(id_A⊗horn.ι)≫R, where R=pr_A≫A.ι≫f. -/
private lemma transHornMap_commonIntersection {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    (A.ι ▷ (SSet.horn 2 (1 : Fin 3) : SSet.{u})) ≫ transHornMap H₀₁ H₁₂ =
      (A : SSet.{u}) ◁ (SSet.horn 2 (1 : Fin 3)).ι ≫ symmStationaryFace f A := by
  apply (horn₂₁TensorLeftIsPushout (A : SSet.{u})).hom_ext
  · calc (A : SSet.{u}) ◁ SSet.horn₂₁.ι₀₁ ≫
          (A.ι ▷ (SSet.horn 2 (1 : Fin 3) : SSet.{u})) ≫ transHornMap H₀₁ H₁₂
        = (A : SSet.{u}) ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫
            symmStationaryFace f A :=
          transHornMap_ι₀₁_stationaryAgree H₀₁ H₁₂
      _ = (A : SSet.{u}) ◁ (SSet.horn₂₁.ι₀₁ ≫
            (SSet.horn 2 (1 : Fin 3)).ι) ≫
            symmStationaryFace f A := by
          rw [← SSet.horn.ι_ι (1 : Fin 3) (2 : Fin 3) (by decide)]
      _ = ((A : SSet.{u}) ◁ SSet.horn₂₁.ι₀₁ ≫
            (A : SSet.{u}) ◁ (SSet.horn 2 (1 : Fin 3)).ι) ≫
            symmStationaryFace f A := by
          rw [MonoidalCategory.whiskerLeft_comp]
      _ = (A : SSet.{u}) ◁ SSet.horn₂₁.ι₀₁ ≫
            (A : SSet.{u}) ◁ (SSet.horn 2 (1 : Fin 3)).ι ≫
              symmStationaryFace f A := by
          rw [Category.assoc]
  · calc (A : SSet.{u}) ◁ SSet.horn₂₁.ι₁₂ ≫
          (A.ι ▷ (SSet.horn 2 (1 : Fin 3) : SSet.{u})) ≫ transHornMap H₀₁ H₁₂
        = (A : SSet.{u}) ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫
            symmStationaryFace f A :=
          transHornMap_ι₁₂_stationaryAgree H₀₁ H₁₂
      _ = (A : SSet.{u}) ◁ (SSet.horn₂₁.ι₁₂ ≫
            (SSet.horn 2 (1 : Fin 3)).ι) ≫
            symmStationaryFace f A := by
          rw [← SSet.horn.ι_ι (1 : Fin 3) (0 : Fin 3) (by decide)]
      _ = ((A : SSet.{u}) ◁ SSet.horn₂₁.ι₁₂ ≫
            (A : SSet.{u}) ◁ (SSet.horn 2 (1 : Fin 3)).ι) ≫
            symmStationaryFace f A := by
          rw [MonoidalCategory.whiskerLeft_comp]
      _ = (A : SSet.{u}) ◁ SSet.horn₂₁.ι₁₂ ≫
            (A : SSet.{u}) ◁ (SSet.horn 2 (1 : Fin 3)).ι ≫
              symmStationaryFace f A := by
          rw [Category.assoc]

/-- For X,Y,S in universe u, p:Y→S, f,g,k:X→Y and A⊆X, let H₀₁:f≃g and H₁₂:g≃k be stationary on A
and over p. The maps J₁ and R glue to Φ₁:U₁→Y, with U₁=(X⊗Λ²₁)∪(A⊗Δ[2])⊆X⊗Δ[2]. -/
private noncomputable def transUnionMap {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    (A.unionProd (SSet.horn 2 (1 : Fin 3)) : SSet.{u}) ⟶ Y :=
  (Subcomplex.unionProd.isPushout A (SSet.horn 2 (1 : Fin 3))).desc
    (transHornMap H₀₁ H₁₂) (symmStationaryFace f A)
    (transHornMap_commonIntersection H₀₁ H₁₂)

/-- For X,Y,S in universe u, p:Y→S, f,g,k:X→Y and A⊆X, let H₀₁:f≃g and H₁₂:g≃k be stationary on A
and over p. The first union inclusion X⊗Λ²₁→U₁ followed by Φ₁ equals J₁. -/
private lemma transUnionMap_ι₁ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫ transUnionMap H₀₁ H₁₂ =
      transHornMap H₀₁ H₁₂ :=
  (Subcomplex.unionProd.isPushout A (SSet.horn 2 (1 : Fin 3))).inl_desc _ _ _

/-- For X,Y,S in universe u, p:Y→S, f,g,k:X→Y and A⊆X, let H₀₁:f≃g and H₁₂:g≃k be stationary on A
and over p. The second union inclusion A⊗Δ[2]→U₁ followed by Φ₁ equals R=pr_A≫A.ι≫f. -/
private lemma transUnionMap_ι₂ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    Subcomplex.unionProd.ι₂ A (SSet.horn 2 (1 : Fin 3)) ≫ transUnionMap H₀₁ H₁₂ =
      symmStationaryFace f A :=
  (Subcomplex.unionProd.isPushout A (SSet.horn 2 (1 : Fin 3))).inr_desc _ _ _

/-- For X,Y,S in universe u, p:Y→S, f,g,k:X→Y and A⊆X, let H₀₁:f≃g and H₁₂:g≃k be stationary on A
and over p. J₁≫p=(id_X⊗horn.ι)≫Q, with Q=pr_X≫f≫p:X⊗Δ[2]→S. -/
private lemma transHornMap_over {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    transHornMap H₀₁ H₁₂ ≫ p =
      (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) ≫ symmBaseMap p f := by
  apply (horn₂₁TensorLeftIsPushout X).hom_ext
  · have hL : (X ◁ SSet.horn₂₁.ι₀₁) ≫ transHornMap H₀₁ H₁₂ ≫ p =
        fst (X : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (f ≫ p) := by
      calc (X ◁ SSet.horn₂₁.ι₀₁) ≫ transHornMap H₀₁ H₁₂ ≫ p
          = ((X ◁ SSet.horn₂₁.ι₀₁) ≫ transHornMap H₀₁ H₁₂) ≫ p := by
            rw [Category.assoc]
        _ = H₀₁.h ≫ p := by
            rw [transHornMap_ι₀₁]
        _ = fst _ _ ≫ (f ≫ p) := H₀₁.over
    have hR : (X ◁ SSet.horn₂₁.ι₀₁) ≫
          (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) ≫ symmBaseMap p f =
        fst (X : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (f ≫ p) := by
      calc (X ◁ SSet.horn₂₁.ι₀₁) ≫
              (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) ≫ symmBaseMap p f
          = ((X ◁ SSet.horn₂₁.ι₀₁) ≫
                X ◁ (SSet.horn 2 (1 : Fin 3)).ι) ≫ symmBaseMap p f := by
            rw [Category.assoc]
        _ = (X ◁ (SSet.horn₂₁.ι₀₁ ≫ (SSet.horn 2 (1 : Fin 3)).ι)) ≫
              symmBaseMap p f := by
            rw [← MonoidalCategory.whiskerLeft_comp]
        _ = (X ◁ stdSimplex.δ (2 : Fin 3)) ≫ symmBaseMap p f := by
            rw [SSet.horn.ι_ι (1 : Fin 3) (2 : Fin 3) (by decide)]
        _ = (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫
              (fst _ _ ≫ (f ≫ p)) := by
            simp only [symmBaseMap]
        _ = ((X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫
              fst _ _) ≫ (f ≫ p) := by
            rw [← Category.assoc]
        _ = fst _ _ ≫ (f ≫ p) := by
            rw [whiskerLeft_fst]
    exact hL.trans hR.symm
  · have hL : (X ◁ SSet.horn₂₁.ι₁₂) ≫ transHornMap H₀₁ H₁₂ ≫ p =
        fst (X : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (f ≫ p) := by
      calc (X ◁ SSet.horn₂₁.ι₁₂) ≫ transHornMap H₀₁ H₁₂ ≫ p
          = ((X ◁ SSet.horn₂₁.ι₁₂) ≫ transHornMap H₀₁ H₁₂) ≫ p := by
            rw [Category.assoc]
        _ = H₁₂.h ≫ p := by
            rw [transHornMap_ι₁₂]
        _ = fst _ _ ≫ (g ≫ p) := H₁₂.over
        _ = fst _ _ ≫ (f ≫ p) := by
            rw [← H₀₁.map_eq]
    have hR : (X ◁ SSet.horn₂₁.ι₁₂) ≫
          (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) ≫ symmBaseMap p f =
        fst (X : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (f ≫ p) := by
      calc (X ◁ SSet.horn₂₁.ι₁₂) ≫
              (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) ≫ symmBaseMap p f
          = ((X ◁ SSet.horn₂₁.ι₁₂) ≫
                X ◁ (SSet.horn 2 (1 : Fin 3)).ι) ≫ symmBaseMap p f := by
            rw [Category.assoc]
        _ = (X ◁ (SSet.horn₂₁.ι₁₂ ≫ (SSet.horn 2 (1 : Fin 3)).ι)) ≫
              symmBaseMap p f := by
            rw [← MonoidalCategory.whiskerLeft_comp]
        _ = (X ◁ stdSimplex.δ (0 : Fin 3)) ≫ symmBaseMap p f := by
            rw [SSet.horn.ι_ι (1 : Fin 3) (0 : Fin 3) (by decide)]
        _ = (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫
              (fst _ _ ≫ (f ≫ p)) := by
            simp only [symmBaseMap]
        _ = ((X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫
              fst _ _) ≫ (f ≫ p) := by
            rw [← Category.assoc]
        _ = fst _ _ ≫ (f ≫ p) := by
            rw [whiskerLeft_fst]
    exact hL.trans hR.symm

/-- For X,Y,S in universe u, p:Y→S, f,g,k:X→Y and A⊆X, let H₀₁:f≃g and H₁₂:g≃k be stationary on A
and over p. For i:U₁→X⊗Δ[2], Φ₁≫p=i≫Q, with Q=pr_X≫f≫p. -/
private lemma transUnionMap_over {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    transUnionMap H₀₁ H₁₂ ≫ p =
      (A.unionProd (SSet.horn 2 (1 : Fin 3))).ι ≫ symmBaseMap p f := by
  apply (Subcomplex.unionProd.isPushout A (SSet.horn 2 (1 : Fin 3))).hom_ext
  · calc Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫
              transUnionMap H₀₁ H₁₂ ≫ p
          = (Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫
              transUnionMap H₀₁ H₁₂) ≫ p := by
            rw [Category.assoc]
        _ = transHornMap H₀₁ H₁₂ ≫ p := by
            rw [transUnionMap_ι₁]
        _ = (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) ≫ symmBaseMap p f := by
            rw [transHornMap_over H₀₁ H₁₂]
        _ = Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫
              (A.unionProd (SSet.horn 2 (1 : Fin 3))).ι ≫
                symmBaseMap p f := by
            rw [Subcomplex.unionProd.ι₁_ι_assoc]
  · calc Subcomplex.unionProd.ι₂ A (SSet.horn 2 (1 : Fin 3)) ≫
              transUnionMap H₀₁ H₁₂ ≫ p
          = (Subcomplex.unionProd.ι₂ A (SSet.horn 2 (1 : Fin 3)) ≫
              transUnionMap H₀₁ H₁₂) ≫ p := by
            rw [Category.assoc]
        _ = symmStationaryFace f A ≫ p := by
            rw [transUnionMap_ι₂]
        _ = (A.ι ▷ (Δ[2] : SSet.{u})) ≫ symmBaseMap p f := by
            rw [symmStationaryFace_over]
        _ = Subcomplex.unionProd.ι₂ A (SSet.horn 2 (1 : Fin 3)) ≫
              (A.unionProd (SSet.horn 2 (1 : Fin 3))).ι ≫
                symmBaseMap p f := by
            rw [Subcomplex.unionProd.ι₂_ι_assoc]

/-- For X,Y,S in universe u, p:Y→S, f,g,k:X→Y and A⊆X, let H₀₁:f≃g and H₁₂:g≃k be stationary on A
and over p. The maps Φ₁:U₁→Y, i:U₁→X⊗Δ[2], p:Y→S and Q=pr_X≫f≫p form the commuting square
Φ₁≫p=i≫Q. -/
private theorem transUnionCommSq {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    CommSq (transUnionMap H₀₁ H₁₂)
      (A.unionProd (SSet.horn 2 (1 : Fin 3))).ι
      p (symmBaseMap p f) :=
  CommSq.mk (transUnionMap_over H₀₁ H₁₂)

/-- For X in universe u and A⊆X, the inclusion (X⊗Λ²₁)∪(A⊗Δ[2])→X⊗Δ[2] is an anodyne extension. -/
private lemma transUnionProd_horn_ι_mem_anodyneExtensions
    {X : SSet.{u}} (A : X.Subcomplex) :
    SSet.anodyneExtensions
      (A.unionProd (SSet.horn 2 (1 : Fin 3))).ι := by
  have hHorn : SSet.anodyneExtensions (SSet.horn 2 (1 : Fin 3)).ι :=
    SSet.anodyneExtensions.horn_ι (1 : Fin 3)
  exact SSet.anodyneExtensions_unionProd_ι A (SSet.horn 2 (1 : Fin 3)) hHorn

/-!
## The selected composition filler

The relative inner-horn union U₁=(X⊗Λ²₁)∪(A⊗Δ[2]) has an anodyne inclusion into X⊗Δ[2].
Fibration lifting gives F₁ extending its glued map and lying over pr_X≫f≫p.
-/

private lemma transUnionProd_horn_ι_hasLiftingProperty
    {X : SSet.{u}} (A : X.Subcomplex)
    {Y S : SSet.{u}} {p : Y ⟶ S} [Fibration p] :
    HasLiftingProperty (A.unionProd (SSet.horn 2 (1 : Fin 3))).ι p :=
  (transUnionProd_horn_ι_mem_anodyneExtensions A) p
    (by rwa [← HomotopicalAlgebra.fibration_iff])

private instance transUnionProd_horn_hasLiftingPropertyInst
    {X : SSet.{u}} {A : X.Subcomplex}
    {Y S : SSet.{u}} {p : Y ⟶ S} [Fibration p] :
    HasLiftingProperty (A.unionProd (SSet.horn 2 (1 : Fin 3))).ι p :=
  transUnionProd_horn_ι_hasLiftingProperty A

/-- For X,Y,S in universe u, p:Y→S, f,g,k:X→Y and A⊆X, let H₀₁:f≃g and H₁₂:g≃k be stationary on A
and over p. If p is a simplicial fibration, the inner-horn lifting square selects F₁:X⊗Δ[2]→Y
extending Φ₁ and lying over Q=pr_X≫f≫p. -/
private noncomputable def transFiller {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    X ⊗ (Δ[2] : SSet.{u}) ⟶ Y :=
  (transUnionCommSq H₀₁ H₁₂).lift

/-- For X,Y,S in universe u, p:Y→S, f,g,k:X→Y and A⊆X, let H₀₁:f≃g and H₁₂:g≃k be stationary on A
and over p. For p a simplicial fibration, F₁≫p=Q=pr_X≫f≫p. -/
private lemma transFiller_over {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    transFiller H₀₁ H₁₂ ≫ p = symmBaseMap p f :=
  (transUnionCommSq H₀₁ H₁₂).fac_right

/-- For X,Y,S in universe u, p:Y→S, f,g,k:X→Y and A⊆X, let H₀₁:f≃g and H₁₂:g≃k be stationary on A
and over p. For p a simplicial fibration and i:U₁→X⊗Δ[2], i≫F₁=Φ₁. -/
private lemma transFiller_union {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    (A.unionProd (SSet.horn 2 (1 : Fin 3))).ι ≫ transFiller H₀₁ H₁₂ =
      transUnionMap H₀₁ H₁₂ :=
  (transUnionCommSq H₀₁ H₁₂).fac_left

/-- For X,Y,S in universe u, p:Y→S, f,g,k:X→Y and A⊆X, let H₀₁:f≃g and H₁₂:g≃k be stationary on A
and over p. For p a simplicial fibration, define G₁=(id_X⊗δ₁)≫F₁:X⊗Δ[1]→Y. The missing 02 edge
gives the composite homotopy f≃k. -/
private noncomputable def transHomotopy {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    X ⊗ (Δ[1] : SSet.{u}) ⟶ Y :=
  (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ transFiller H₀₁ H₁₂

/-- For Λ²₁⊆Δ[2] in universe u, δ₂:Δ[1]→Δ[2] equals the 01 edge inclusion into the horn followed by
horn.ι. -/
private lemma trans_delta₂_eq :
    (stdSimplex.δ (2 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) =
      SSet.horn₂₁.ι₀₁ ≫ (SSet.horn 2 (1 : Fin 3)).ι := by
  rw [← SSet.horn.ι_ι (1 : Fin 3) (2 : Fin 3) (by decide)]

/-- For X in universe u, id_X⊗δ₂ is the composite X⊗Δ[1]→X⊗Λ²₁→X⊗Δ[2] through the horn's 01 edge. -/
private lemma trans_whisker_δ₂ {X : SSet.{u}} :
    (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) =
      (X ◁ SSet.horn₂₁.ι₀₁) ≫ (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) := by
  calc (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]))
      = X ◁ (SSet.horn₂₁.ι₀₁ ≫ (SSet.horn 2 (1 : Fin 3)).ι) := by
        rw [trans_delta₂_eq]
    _ = (X ◁ SSet.horn₂₁.ι₀₁) ≫ (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) := by
        rw [MonoidalCategory.whiskerLeft_comp]

/-- For X in universe u and A⊆X, X⊗Λ²₁→X⊗Δ[2] is the first union inclusion X⊗Λ²₁→U₁ followed by
U₁→X⊗Δ[2]. -/
private lemma trans_horn_whisker_eq_unionProd {X : SSet.{u}}
    (A : X.Subcomplex) :
    (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) =
      Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫
        (A.unionProd (SSet.horn 2 (1 : Fin 3))).ι := by
  rw [← Subcomplex.unionProd.ι₁_ι]

private lemma transHomotopy_ι₀ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    SSet.ι₀ ≫ transHomotopy H₀₁ H₁₂ = f := by
  calc SSet.ι₀ ≫ transHomotopy H₀₁ H₁₂
      = SSet.ι₀ ≫ (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ transFiller H₀₁ H₁₂ := rfl
    _ = (SSet.ι₀ ≫ (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]))) ≫ transFiller H₀₁ H₁₂ := by
        rw [Category.assoc]
    _ = (SSet.ι₀ ≫ (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]))) ≫ transFiller H₀₁ H₁₂ := by
        rw [symm_iota₀_δ₁_eq_δ₂]
    _ = SSet.ι₀ ≫ (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ transFiller H₀₁ H₁₂ := by
        rw [Category.assoc]
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₁.ι₀₁ ≫ (X ◁ (SSet.horn 2 (1 : Fin 3)).ι)) ≫
        transFiller H₀₁ H₁₂ := by
        rw [trans_whisker_δ₂]
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₁.ι₀₁) ≫
        (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) ≫ transFiller H₀₁ H₁₂ := by
        simp only [Category.assoc]
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₁.ι₀₁) ≫
        (Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫
          (A.unionProd (SSet.horn 2 (1 : Fin 3))).ι) ≫ transFiller H₀₁ H₁₂ := by
        rw [trans_horn_whisker_eq_unionProd A]
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₁.ι₀₁) ≫
        Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫
          ((A.unionProd (SSet.horn 2 (1 : Fin 3))).ι ≫ transFiller H₀₁ H₁₂) := by
        simp only [Category.assoc]
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₁.ι₀₁) ≫
        Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫
          transUnionMap H₀₁ H₁₂ := by
        rw [transFiller_union H₀₁ H₁₂]
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₁.ι₀₁) ≫
        (Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫ transUnionMap H₀₁ H₁₂) := rfl
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₁.ι₀₁) ≫ transHornMap H₀₁ H₁₂ := by
        rw [transUnionMap_ι₁]
    _ = SSet.ι₀ ≫ ((X ◁ SSet.horn₂₁.ι₀₁) ≫ transHornMap H₀₁ H₁₂) := rfl
    _ = SSet.ι₀ ≫ H₀₁.h := by
        rw [transHornMap_ι₀₁]
    _ = f := by
        rw [H₀₁.h₀]

/-- For Λ²₁⊆Δ[2] in universe u, δ₀:Δ[1]→Δ[2] equals the 12 edge inclusion into the horn followed by
horn.ι. -/
private lemma trans_delta₀_eq :
    (stdSimplex.δ (0 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) =
      SSet.horn₂₁.ι₁₂ ≫ (SSet.horn 2 (1 : Fin 3)).ι := by
  rw [← SSet.horn.ι_ι (1 : Fin 3) (0 : Fin 3) (by decide)]

/-- For X in universe u, id_X⊗δ₀ is the composite X⊗Δ[1]→X⊗Λ²₁→X⊗Δ[2] through the horn's 12 edge. -/
private lemma trans_whisker_δ₀ {X : SSet.{u}} :
    (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) =
      (X ◁ SSet.horn₂₁.ι₁₂) ≫ (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) := by
  calc (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2]))
      = X ◁ (SSet.horn₂₁.ι₁₂ ≫ (SSet.horn 2 (1 : Fin 3)).ι) := by
        rw [trans_delta₀_eq]
    _ = (X ◁ SSet.horn₂₁.ι₁₂) ≫ (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) := by
        rw [MonoidalCategory.whiskerLeft_comp]

/-- In universe u, δ₁:Δ[1]→Δ[2] sends geometric vertex 1 to vertex 2. -/
private lemma trans_δ₁_one :
    (stdSimplex.δ (1 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]).app _
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2) : (Δ[1] : SSet.{u}) _⦋0⦌) =
      stdSimplex.obj₀Equiv.symm (2 : Fin 3) := rfl

/-- In universe u, δ₀:Δ[1]→Δ[2] sends geometric vertex 1 to vertex 2. -/
private lemma trans_δ₀_one :
    (stdSimplex.δ (0 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]).app _
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2) : (Δ[1] : SSet.{u}) _⦋0⦌) =
      stdSimplex.obj₀Equiv.symm (2 : Fin 3) := rfl

/-- For X in universe u, ι₁≫(id_X⊗δ₁)=ι₁≫(id_X⊗δ₀):X→X⊗Δ[2], because both composites have
second-coordinate vertex 2. -/
private lemma trans_iota₁_δ₁_eq_δ₀ {X : SSet.{u}} :
    SSet.ι₁ ≫ (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) =
      SSet.ι₁ ≫ (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) := by
  calc SSet.ι₁ (X := X) ≫ (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]))
      = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ≫
            (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) := by
        rw [← CartesianMonoidalCategory.lift_whiskerLeft]
        rfl
    _ = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const
            ((stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]).app _
              (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) := by
        rw [SSet.const_comp]
    _ = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const (stdSimplex.obj₀Equiv.symm (2 : Fin 3) : (Δ[2] : SSet.{u}) _⦋0⦌)) := by
        rw [trans_δ₁_one]
    _ = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const
            ((stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2]).app _
              (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) := by
        rw [trans_δ₀_one]
    _ = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ≫
            (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) := by
        rw [SSet.const_comp]
    _ = SSet.ι₁ (X := X) ≫ (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) := by
        rw [← CartesianMonoidalCategory.lift_whiskerLeft]
        rfl

private lemma transHomotopy_ι₁ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    SSet.ι₁ ≫ transHomotopy H₀₁ H₁₂ = h := by
  calc SSet.ι₁ ≫ transHomotopy H₀₁ H₁₂
      = SSet.ι₁ ≫ (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ transFiller H₀₁ H₁₂ := rfl
    _ = (SSet.ι₁ ≫ (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]))) ≫ transFiller H₀₁ H₁₂ := by
        rw [Category.assoc]
    _ = (SSet.ι₁ ≫ (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2]))) ≫ transFiller H₀₁ H₁₂ := by
        rw [trans_iota₁_δ₁_eq_δ₀]
    _ = SSet.ι₁ ≫ (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ transFiller H₀₁ H₁₂ := by
        rw [Category.assoc]
    _ = SSet.ι₁ ≫ (X ◁ SSet.horn₂₁.ι₁₂ ≫ (X ◁ (SSet.horn 2 (1 : Fin 3)).ι)) ≫
        transFiller H₀₁ H₁₂ := by
        rw [trans_whisker_δ₀]
    _ = SSet.ι₁ ≫ (X ◁ SSet.horn₂₁.ι₁₂) ≫
        (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) ≫ transFiller H₀₁ H₁₂ := by
        simp only [Category.assoc]
    _ = SSet.ι₁ ≫ (X ◁ SSet.horn₂₁.ι₁₂) ≫
        (Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫
          (A.unionProd (SSet.horn 2 (1 : Fin 3))).ι) ≫ transFiller H₀₁ H₁₂ := by
        rw [trans_horn_whisker_eq_unionProd A]
    _ = SSet.ι₁ ≫ (X ◁ SSet.horn₂₁.ι₁₂) ≫
        Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫
          ((A.unionProd (SSet.horn 2 (1 : Fin 3))).ι ≫ transFiller H₀₁ H₁₂) := by
        simp only [Category.assoc]
    _ = SSet.ι₁ ≫ (X ◁ SSet.horn₂₁.ι₁₂) ≫
        Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫
          transUnionMap H₀₁ H₁₂ := by
        rw [transFiller_union H₀₁ H₁₂]
    _ = SSet.ι₁ ≫ (X ◁ SSet.horn₂₁.ι₁₂) ≫
        (Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫ transUnionMap H₀₁ H₁₂) := rfl
    _ = SSet.ι₁ ≫ (X ◁ SSet.horn₂₁.ι₁₂) ≫ transHornMap H₀₁ H₁₂ := by
        rw [transUnionMap_ι₁]
    _ = SSet.ι₁ ≫ ((X ◁ SSet.horn₂₁.ι₁₂) ≫ transHornMap H₀₁ H₁₂) := rfl
    _ = SSet.ι₁ ≫ H₁₂.h := by
        rw [transHornMap_ι₁₂]
    _ = h := by
        rw [H₁₂.h₁]

/-!
## The composite edge and its relative conditions

Restrict F₁ along δ₁, the missing 02 edge. This gives f≃k; the stationary restriction is the
f-map on A, and the base projection is pr_X≫f≫p.
-/

/-- For X,Y,S in universe u, p:Y→S, f,g,k:X→Y and A⊆X, let H₀₁:f≃g and H₁₂:g≃k be stationary on A
and over p. For p a simplicial fibration, restricting F₁ to A⊗Δ[2] gives R=pr_A≫A.ι≫f. -/
private lemma transFiller_restrict {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    (A.ι ▷ (Δ[2] : SSet.{u})) ≫ transFiller H₀₁ H₁₂ = symmStationaryFace f A := by
  calc (A.ι ▷ (Δ[2] : SSet.{u})) ≫ transFiller H₀₁ H₁₂
      = (Subcomplex.unionProd.ι₂ A (SSet.horn 2 (1 : Fin 3)) ≫
          (A.unionProd (SSet.horn 2 (1 : Fin 3))).ι) ≫ transFiller H₀₁ H₁₂ := by
        rw [← Subcomplex.unionProd.ι₂_ι]
    _ = Subcomplex.unionProd.ι₂ A (SSet.horn 2 (1 : Fin 3)) ≫
          ((A.unionProd (SSet.horn 2 (1 : Fin 3))).ι ≫ transFiller H₀₁ H₁₂) := by
        rw [Category.assoc]
    _ = Subcomplex.unionProd.ι₂ A (SSet.horn 2 (1 : Fin 3)) ≫ transUnionMap H₀₁ H₁₂ := by
        rw [transFiller_union H₀₁ H₁₂]
    _ = symmStationaryFace f A := by
        rw [transUnionMap_ι₂ H₀₁ H₁₂]

/-- For X,Y,S in universe u, p:Y→S, f,g,k:X→Y and A⊆X, let H₀₁:f≃g and H₁₂:g≃k be stationary on A
and over p. For p a simplicial fibration, G₁=(id_X⊗δ₁)≫F₁ satisfies the c-component of G₁ sends
(a,t) to f_c(a) for every a∈A_c and t∈Δ[1]_c. -/
private lemma transHomotopy_stationary {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A)
    {n : SimplexCategoryᵒᵖ} {x : X.obj n} (hx : x ∈ A.obj n)
    (t : (Δ[1] : SSet.{u}).obj n) :
    (transHomotopy H₀₁ H₁₂).app n ⟨x, t⟩ = f.app n x := by
  have h_whisker_δ₁ : (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])).app n ⟨x, t⟩ =
      ⟨x, (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ := rfl
  have h_filler : (transFiller H₀₁ H₁₂).app n
      ⟨x, (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ = f.app n x := by
    have hA : (A.ι ▷ (Δ[2] : SSet.{u})).app n
        ⟨⟨x, hx⟩, (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ =
        ⟨x, (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ := rfl
    calc (transFiller H₀₁ H₁₂).app n
          ⟨x, (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩
        = (transFiller H₀₁ H₁₂).app n
            ((A.ι ▷ (Δ[2] : SSet.{u})).app n
              ⟨⟨x, hx⟩, (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩) := by
          rw [hA]
      _ = ((A.ι ▷ (Δ[2] : SSet.{u})) ≫ transFiller H₀₁ H₁₂).app n
            ⟨⟨x, hx⟩, (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ := rfl
      _ = (symmStationaryFace f A).app n
            ⟨⟨x, hx⟩, (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ := by
          rw [transFiller_restrict H₀₁ H₁₂]
      _ = f.app n x := rfl
  calc (transHomotopy H₀₁ H₁₂).app n ⟨x, t⟩
      = ((X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ transFiller H₀₁ H₁₂).app n
          ⟨x, t⟩ := rfl
    _ = (transFiller H₀₁ H₁₂).app n
          ((X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])).app n ⟨x, t⟩) := rfl
    _ = (transFiller H₀₁ H₁₂).app n
          ⟨x, (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ := by
        rw [h_whisker_δ₁]
    _ = f.app n x := h_filler

private lemma transHomotopy_over {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    transHomotopy H₀₁ H₁₂ ≫ p = fst _ _ ≫ (f ≫ p) := by
  calc transHomotopy H₀₁ H₁₂ ≫ p
      = (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫ transFiller H₀₁ H₁₂) ≫ p := rfl
    _ = (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ (transFiller H₀₁ H₁₂ ≫ p) := by
        rw [Category.assoc]
    _ = (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ symmBaseMap p f := by
        rw [transFiller_over H₀₁ H₁₂]
    _ = (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫
          (fst X _ ≫ (f ≫ p)) := by
        simp only [symmBaseMap]
    _ = ((X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ fst X _) ≫ (f ≫ p) := by
        rw [Category.assoc]
    _ = fst _ _ ≫ (f ≫ p) := by
        rw [whiskerLeft_fst]

/-- For X,Y,S in universe u, p:Y→S, f,g,k:X→Y and A⊆X, let H₀₁:f≃g and H₁₂:g≃k be stationary on A
and over p. If p is a simplicial fibration, the inner-horn construction gives a composite f≃k,
stationary on A, with base composite pr_X≫f≫p. -/
@[no_expose]
noncomputable def trans {h : X ⟶ Y} [Fibration p]
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    HomotopyRelOver p f h A where
  toHomotopyRel :=
    { h := transHomotopy H₀₁ H₁₂
      h₀ := transHomotopy_ι₀ H₀₁ H₁₂
      h₁ := transHomotopy_ι₁ H₀₁ H₁₂
      stationary := fun _ hx t => transHomotopy_stationary H₀₁ H₁₂ hx t }
  over := transHomotopy_over H₀₁ H₁₂

end HomotopyRelOver

end SSet

end
