/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MinimalFibration.Basic

@[expose] public section

/-!
# Map-level fiberwise homotopy and simplex over-relations

For p:E→B and p′:E′→B, a fiberwise homotopy of maps f,g:E→E′ is a cylinder H:E×Δ[1]→E′ with
those endpoints and H≫p′=pr₁≫p. It gives both endpoint maps over B; a map over B has its
constant reflexive homotopy.

For n-simplices x,y over p:X→S, an over-relation additionally specifies a base simplex β:Δ[n]→S
and common boundary d:∂Δ[n]→X. The cylinder is stationary on the boundary and projects to β
independently of the interval. The base simplex may be arbitrary. Its endpoint base and boundary
equations give a relative fiberwise simplex homotopy, and minimality of p then gives x=y.

All simplicial sets lie in an arbitrary universe u.

References: Goerss–Jardine, Simplicial Homotopy Theory, Chapter I, Section 10; Hovey, Model Categories, Section 3.5.
-/

open CategoryTheory Simplicial SSet
open MonoidalCategory CartesianMonoidalCategory

namespace SSet

universe u

variable {E E' B : SSet.{u}}

/-- Let p:E→B and p′:E′→B be simplicial maps, and f,g:E→E′. A map-level fiberwise homotopy has a
cylinder H:E×Δ[1]→E′ with endpoints f,g and H≫p′=pr₁≫p, so the base value is fixed throughout
the interval. -/
structure FiberwiseHomotopy (p : E ⟶ B) (p' : E' ⟶ B) (f g : E ⟶ E') where
  /-- Let p:E→B and p′:E′→B be simplicial maps, and f,g:E→E′. The homotopy component is the cylinder
E×Δ[1]→E′ with endpoint zero f and endpoint one g. -/
  hom : Homotopy f g
  /-- Let p:E→B and p′:E′→B be simplicial maps, and f,g:E→E′. The cylinder H of a fiberwise homotopy
satisfies H≫p′=pr₁≫p. -/
  over : hom.h ≫ p' = fst _ _ ≫ p

namespace FiberwiseHomotopy

variable {p : E ⟶ B} {p' : E' ⟶ B} {f g : E ⟶ E'}

/-- Let p:E→B and p′:E′→B be simplicial maps, and f,g:E→E′. A fiberwise homotopy from f to g gives
f≫p′=p at endpoint zero. -/
lemma fac₀ (H : FiberwiseHomotopy (p := p) (p' := p') (f := f) (g := g)) :
    f ≫ p' = p := by
  have h₀ : (SSet.ι₀ ≫ H.hom.h) ≫ p' = f ≫ p' := by rw [H.hom.h₀]
  have hbase : (SSet.ι₀ ≫ H.hom.h) ≫ p' = p := by
    calc (SSet.ι₀ ≫ H.hom.h) ≫ p'
        = SSet.ι₀ ≫ (H.hom.h ≫ p') := by rw [Category.assoc]
      _ = SSet.ι₀ ≫ (fst _ _ ≫ p) := by rw [H.over]
      _ = (SSet.ι₀ ≫ fst _ _) ≫ p := by rw [Category.assoc]
      _ = p := by rw [SSet.ι₀_fst, Category.id_comp]
  exact h₀.symm.trans hbase

/-- Let p:E→B and p′:E′→B be simplicial maps, and f,g:E→E′. A fiberwise homotopy from f to g gives
g≫p′=p at endpoint one. -/
lemma fac₁ (H : FiberwiseHomotopy (p := p) (p' := p') (f := f) (g := g)) :
    g ≫ p' = p := by
  have h₁ : (SSet.ι₁ ≫ H.hom.h) ≫ p' = g ≫ p' := by rw [H.hom.h₁]
  have hbase : (SSet.ι₁ ≫ H.hom.h) ≫ p' = p := by
    calc (SSet.ι₁ ≫ H.hom.h) ≫ p'
        = SSet.ι₁ ≫ (H.hom.h ≫ p') := by rw [Category.assoc]
      _ = SSet.ι₁ ≫ (fst _ _ ≫ p) := by rw [H.over]
      _ = (SSet.ι₁ ≫ fst _ _) ≫ p := by rw [Category.assoc]
      _ = p := by rw [SSet.ι₁_fst, Category.id_comp]
  exact h₁.symm.trans hbase

/-- For p:E→B, p′:E′→B and f:E→E′ satisfying f≫p′=p, the constant cylinder on f is a map-level
fiberwise homotopy f→f. -/
def refl (f : E ⟶ E') (hfac : f ≫ p' = p) :
    FiberwiseHomotopy (p := p) (p' := p') (f := f) (g := f) where
  hom :=
    { h := fst _ _ ≫ f
      h₀ := by simp
      h₁ := by simp
      rel := by ext n ⟨⟨x, hx⟩, t⟩; cases hx }
  over := by
    change (fst _ _ ≫ f) ≫ p' = fst _ _ ≫ p
    rw [Category.assoc, hfac]

end FiberwiseHomotopy

namespace MinimalFibration

variable {X S : SSet.{u}}

/-- Let p:X→S be a simplicial map and x,y n-simplices, represented by x̄,ȳ:Δ[n]→X. An over-relation
consists of a boundary-stationary cylinder H:x̄→ȳ, a base simplex β:Δ[n]→S and boundary value
d:∂Δ[n]→X, with H≫p=pr₁≫β and ∂x=d. The base simplex may vary on Δ[n]; only its interval
coordinate is constant. The target boundary and base equations follow from the cylinder
conditions. -/
@[ext]
structure OverRelation {n : ℕ} (p : X ⟶ S) (x y : X _⦋n⦌) where
  /-- Let p:X→S be a simplicial map and x,y n-simplices, represented by x̄,ȳ:Δ[n]→X. An
over-relation consists of a boundary-stationary cylinder H:x̄→ȳ, a base simplex β:Δ[n]→S and
boundary value d:∂Δ[n]→X, with H≫p=pr₁≫β and ∂x=d. The homotopy component is stationary on
∂Δ[n]×Δ[1]. -/
  hom : HomotopyRel (yonedaEquiv.symm x) (yonedaEquiv.symm y) (SSet.boundary n)
  /-- Let p:X→S be a simplicial map and x,y n-simplices, represented by x̄,ȳ:Δ[n]→X. An
over-relation consists of a boundary-stationary cylinder H:x̄→ȳ, a base simplex β:Δ[n]→S and
boundary value d:∂Δ[n]→X, with H≫p=pr₁≫β and ∂x=d. The base component is the map β:Δ[n]→S to
which both endpoint simplices project. -/
  base : Δ[n] ⟶ S
  /-- Let p:X→S be a simplicial map and x,y n-simplices, represented by x̄,ȳ:Δ[n]→X. An
over-relation consists of a boundary-stationary cylinder H:x̄→ȳ, a base simplex β:Δ[n]→S and
boundary value d:∂Δ[n]→X, with H≫p=pr₁≫β and ∂x=d. The boundary component is the map d:∂Δ[n]→X
shared by both endpoint simplices. -/
  bd : (SSet.boundary n : SSet.{u}) ⟶ X
  /-- Let p:X→S be a simplicial map and x,y n-simplices, represented by x̄,ȳ:Δ[n]→X. An
over-relation consists of a boundary-stationary cylinder H:x̄→ȳ, a base simplex β:Δ[n]→S and
boundary value d:∂Δ[n]→X, with H≫p=pr₁≫β and ∂x=d. The cylinder projection is H≫p=pr₁≫β. -/
  over : hom.h ≫ p = fst _ _ ≫ base
  /-- Let p:X→S be a simplicial map and x,y n-simplices, represented by x̄,ȳ:Δ[n]→X. An
over-relation consists of a boundary-stationary cylinder H:x̄→ȳ, a base simplex β:Δ[n]→S and
boundary value d:∂Δ[n]→X, with H≫p=pr₁≫β and ∂x=d. The source simplex satisfies ∂Δ[n]→Δ[n]→X
equal to d. -/
  boundary : (SSet.boundary n).ι ≫ yonedaEquiv.symm x = bd

namespace OverRelation

variable {p : X ⟶ S} {n : ℕ} {x y : X _⦋n⦌}

/-- Let p:X→S be a simplicial map and x,y n-simplices, represented by x̄,ȳ:Δ[n]→X. An over-relation
consists of a boundary-stationary cylinder H:x̄→ȳ, a base simplex β:Δ[n]→S and boundary value
d:∂Δ[n]→X, with H≫p=pr₁≫β and ∂x=d. The source simplex satisfies x̄≫p=β. -/
lemma base_left (W : OverRelation (n := n) p x y) :
    yonedaEquiv.symm x ≫ p = W.base := by
  have h₀ : (SSet.ι₀ ≫ W.hom.h) ≫ p = yonedaEquiv.symm x ≫ p := by
    rw [W.hom.h₀]
  have hbase : (SSet.ι₀ ≫ W.hom.h) ≫ p = W.base := by
    calc (SSet.ι₀ ≫ W.hom.h) ≫ p
        = SSet.ι₀ ≫ (W.hom.h ≫ p) := by rw [Category.assoc]
      _ = SSet.ι₀ ≫ (fst _ _ ≫ W.base) := by rw [W.over]
      _ = (SSet.ι₀ ≫ fst _ _) ≫ W.base := by rw [Category.assoc]
      _ = W.base := by rw [SSet.ι₀_fst, Category.id_comp]
  exact h₀.symm.trans hbase

/-- Let p:X→S be a simplicial map and x,y n-simplices, represented by x̄,ȳ:Δ[n]→X. An over-relation
consists of a boundary-stationary cylinder H:x̄→ȳ, a base simplex β:Δ[n]→S and boundary value
d:∂Δ[n]→X, with H≫p=pr₁≫β and ∂x=d. The target simplex satisfies ȳ≫p=β. -/
lemma base_right (W : OverRelation (n := n) p x y) :
    yonedaEquiv.symm y ≫ p = W.base := by
  have h₁ : (SSet.ι₁ ≫ W.hom.h) ≫ p = yonedaEquiv.symm y ≫ p := by
    rw [W.hom.h₁]
  have hbase : (SSet.ι₁ ≫ W.hom.h) ≫ p = W.base := by
    calc (SSet.ι₁ ≫ W.hom.h) ≫ p
        = SSet.ι₁ ≫ (W.hom.h ≫ p) := by rw [Category.assoc]
      _ = SSet.ι₁ ≫ (fst _ _ ≫ W.base) := by rw [W.over]
      _ = (SSet.ι₁ ≫ fst _ _) ≫ W.base := by rw [Category.assoc]
      _ = W.base := by rw [SSet.ι₁_fst, Category.id_comp]
  exact h₁.symm.trans hbase

/-- Let p:X→S be a simplicial map and x,y n-simplices, represented by x̄,ȳ:Δ[n]→X. An over-relation
consists of a boundary-stationary cylinder H:x̄→ȳ, a base simplex β:Δ[n]→S and boundary value
d:∂Δ[n]→X, with H≫p=pr₁≫β and ∂x=d. The two endpoint simplices have the same restriction to
∂Δ[n]. -/
lemma boundary_eq (W : OverRelation (n := n) p x y) :
    (SSet.boundary n).ι ≫ yonedaEquiv.symm x =
      (SSet.boundary n).ι ≫ yonedaEquiv.symm y := by
  ext m ⟨a, ha⟩
  change (yonedaEquiv.symm x).app m a = (yonedaEquiv.symm y).app m a
  have h_app_y : W.hom.h.app m (SSet.ι₁.app m a) =
      (yonedaEquiv.symm y).app m a := by
    calc W.hom.h.app m (SSet.ι₁.app m a)
        = (SSet.ι₁ ≫ W.hom.h).app m a := rfl
      _ = (yonedaEquiv.symm y).app m a := by rw [W.hom.h₁]
  have h_fst : (SSet.ι₁.app m a).1 = a := by simp
  have h_pair : SSet.ι₁.app m a = ⟨a, (SSet.ι₁.app m a).2⟩ := by
    apply Prod.ext
    · exact h_fst
    · rfl
  have h_stat : W.hom.h.app m (SSet.ι₁.app m a) =
      (yonedaEquiv.symm x).app m a := by
    calc W.hom.h.app m (SSet.ι₁.app m a)
        = W.hom.h.app m ⟨a, (SSet.ι₁.app m a).2⟩ := by rw [h_pair]
      _ = (yonedaEquiv.symm x).app m a := W.hom.stationary a ha _
  exact h_stat.symm.trans h_app_y

/-- Let p:X→S be a simplicial map and x,y n-simplices, represented by x̄,ȳ:Δ[n]→X. An over-relation
consists of a boundary-stationary cylinder H:x̄→ȳ, a base simplex β:Δ[n]→S and boundary value
d:∂Δ[n]→X, with H≫p=pr₁≫β and ∂x=d. The target simplex has boundary restriction d. -/
lemma boundary_right (W : OverRelation (n := n) p x y) :
    (SSet.boundary n).ι ≫ yonedaEquiv.symm y = W.bd := by
  rw [← W.boundary_eq, W.boundary]

/-- Let p:X→S be a simplicial map and x,y n-simplices, represented by x̄,ȳ:Δ[n]→X. An over-relation
consists of a boundary-stationary cylinder H:x̄→ȳ, a base simplex β:Δ[n]→S and boundary value
d:∂Δ[n]→X, with H≫p=pr₁≫β and ∂x=d. These maps form the commuting square with top H, left pr₁,
right p and bottom β. -/
theorem overSquare (W : OverRelation (n := n) p x y) :
    CommSq W.hom.h (fst _ _) p W.base :=
  CommSq.mk W.over

/-- Let p:X→S be a simplicial map and x,y n-simplices, represented by x̄,ȳ:Δ[n]→X. The constant
cylinder on x gives an over-relation from x to itself, with base x̄≫p and boundary ∂x. -/
noncomputable def refl (x : X _⦋n⦌) :
    OverRelation (n := n) (p := p) (x := x) (y := x) where
  hom := HomotopyRel.refl (yonedaEquiv.symm x) (SSet.boundary n)
  base := yonedaEquiv.symm x ≫ p
  bd := (SSet.boundary n).ι ≫ yonedaEquiv.symm x
  over := by
    calc (HomotopyRel.refl (yonedaEquiv.symm x) (SSet.boundary n)).h ≫ p
        _ = (fst _ _ ≫ yonedaEquiv.symm x) ≫ p := rfl
        _ = fst _ _ ≫ (yonedaEquiv.symm x ≫ p) := Category.assoc _ _ _
  boundary := rfl

/-- Let p:X→S be a simplicial map and x,y n-simplices, represented by x̄,ȳ:Δ[n]→X. An over-relation
consists of a boundary-stationary cylinder H:x̄→ȳ, a base simplex β:Δ[n]→S and boundary value
d:∂Δ[n]→X, with H≫p=pr₁≫β and ∂x=d. Since β=x̄≫p, the same cylinder gives the fiberwise simplex
homotopy relative to ∂Δ[n]. -/
def toFiberwiseHomotopy (W : OverRelation (n := n) p x y) :
    FiberwiseHomotopy (n := n) p x y where
  homotopyRel := W.hom
  over := by
    calc W.hom.h ≫ p
        = fst _ _ ≫ W.base := W.over
      _ = fst _ _ ≫ (yonedaEquiv.symm x ≫ p) := by rw [W.base_left]

/-- Let p:X→S be a simplicial map and x,y n-simplices, represented by x̄,ȳ:Δ[n]→X. An over-relation
consists of a boundary-stationary cylinder H:x̄→ȳ, a base simplex β:Δ[n]→S and boundary value
d:∂Δ[n]→X, with H≫p=pr₁≫β and ∂x=d. If p is minimal, the endpoint simplices are equal: their
base and boundary values agree and the cylinder gives the required relative fiberwise homotopy. -/
theorem eq (hmin : IsMinimal p) (W : OverRelation (n := n) p x y) : x = y := by
  apply hmin
  · exact W.toFiberwiseHomotopy.base_app_eq
  · exact W.boundary.trans W.boundary_right.symm
  · exact ⟨W.toFiberwiseHomotopy⟩

end OverRelation

end MinimalFibration

end SSet
