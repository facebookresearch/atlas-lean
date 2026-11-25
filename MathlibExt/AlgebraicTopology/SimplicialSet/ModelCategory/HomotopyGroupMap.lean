/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.KanComplex.HomotopyGroup

/-!
# Homotopy group maps

This module defines the pointed-simplex pushforward `PtSimplex.map` and the
induced maps `KanComplex.π.map` on homotopy groups of Kan complexes. It proves
the identity, composition, map-congruence and pointed-square laws for these maps,
multiplicativity of `π.map` in
positive degree (`π.map_mul` and `SSet.KanComplex.π.mapHom` with
`mapHom_apply`, `mapHom_id`, `mapHom_comp`) and preservation of the unit in every
degree (`π.map_one`), and constructs the equivalences
`KanComplex.π.equivOfIso` induced by simplicial-set isomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SSet

namespace PtSimplex

variable {X Y Z : SSet.{u}} {n : ℕ} {x : X _⦋0⦌} {y : Y _⦋0⦌} {z : Z _⦋0⦌}

/-- Pushforward of a pointed simplex along `f : X ⟶ Y` sending `x` to `y`. -/
def map (f : X ⟶ Y) (h : f.app _ x = y) (p : X.PtSimplex n x) : Y.PtSimplex n y :=
  p.comp (RelativeMorphism.ofSimplex₀ f x y h) rfl

@[simp]
lemma map_id (p : X.PtSimplex n x) : PtSimplex.map (𝟙 X) rfl p = p := by
  apply RelativeMorphism.ext
  ext m a
  rfl

lemma map_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z)
    (hx : f.app _ x = y) (hy : g.app _ y = z) (h : (f ≫ g).app _ x = z)
    (p : X.PtSimplex n x) :
    PtSimplex.map (f ≫ g) h p = PtSimplex.map g hy (PtSimplex.map f hx p) := by
  apply RelativeMorphism.ext
  ext m a
  rfl

lemma map_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hx : f.app _ x = y) (hy : g.app _ y = z)
    (p : X.PtSimplex n x) :
    PtSimplex.map (f ≫ g) (by simp [hx, hy]) p =
      PtSimplex.map g hy (PtSimplex.map f hx p) := by
  apply RelativeMorphism.ext
  ext m a
  rfl

end PtSimplex

namespace KanComplex

namespace π

variable {X Y Z : SSet.{u}} {n : ℕ} {x : X _⦋0⦌} {y : Y _⦋0⦌} {z : Z _⦋0⦌}

/-- Functorial pushforward on homotopy groups along `f : X ⟶ Y`
sending the base point `x` to `y`. -/
def map (f : X ⟶ Y) (h : f.app _ x = y) (n : ℕ) : π n X x → π n Y y :=
  fun q => q.postcomp (RelativeMorphism.ofSimplex₀ f x y h) rfl

/-- Equal pointed simplicial maps induce the same entire homotopy-group map in every degree. -/
lemma map_congr {f g : X ⟶ Y} (hfg : f = g)
    (hf : f.app _ x = y) (hg : g.app _ x = y) (n : ℕ) :
    map f hf n = map g hg n := by
  cases hfg
  rfl

/-- Alias for `map f h n`. -/
abbrev mapπ (f : X ⟶ Y) (h : f.app _ x = y) (n : ℕ) : π n X x → π n Y y :=
  map f h n

@[simp]
lemma map_mk (f : X ⟶ Y) (h : f.app _ x = y) (p : X.PtSimplex n x) :
    map f h n (mk p) = mk (PtSimplex.map f h p) :=
  rfl

@[simp]
lemma map_id_apply (q : π n X x) : map (𝟙 X) rfl n q = q := by
  induction q using rec with
  | mk p =>
    change mk (PtSimplex.map (𝟙 X) rfl p) = mk p
    rw [PtSimplex.map_id]

lemma map_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z)
    (hx : f.app _ x = y) (hy : g.app _ y = z) (h : (f ≫ g).app _ x = z)
    (q : π n X x) :
    map (f ≫ g) h n q = map g hy n (map f hx n q) := by
  induction q using rec with
  | mk p => simp [PtSimplex.map_comp_apply f g hx hy h]

lemma map_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hx : f.app _ x = y) (hy : g.app _ y = z)
    (q : π n X x) :
    map (f ≫ g) (by simp [hx, hy]) n q =
      map g hy n (map f hx n q) := by
  induction q using rec with
  | mk p => simp [PtSimplex.map_comp f g hx hy]

/-- A pointed commutative simplicial square induces a commutative homotopy-group square. -/
lemma map_square {W : SSet.{u}} {w : W _⦋0⦌}
    (f : X ⟶ Y) (g : Z ⟶ W) (a : X ⟶ Z) (b : Y ⟶ W)
    (hSquare : a ≫ g = f ≫ b)
    (hf : f.app _ x = y) (hg : g.app _ z = w)
    (ha : a.app _ x = z) (hb : b.app _ y = w)
    (n : ℕ) (q : π n X x) :
    map g hg n (map a ha n q) = map b hb n (map f hf n q) := by
  have hLeft : (a ≫ g).app _ x = w := by
    change g.app _ (a.app _ x) = w
    rw [ha, hg]
  have hRight : (f ≫ b).app _ x = w := by
    change b.app _ (f.app _ x) = w
    rw [hf, hb]
  exact (map_comp_apply a g ha hg hLeft q).symm.trans
    ((congrFun (map_congr hSquare hLeft hRight n) q).trans
      (map_comp_apply f b hf hb hRight q))

lemma map_mul {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (f : X ⟶ Y) (h : f.app _ x = y) (n : ℕ)
    (a b : π (n + 1) X x) :
    π.map f h (n + 1) (a * b) =
      π.map f h (n + 1) a * π.map f h (n + 1) b := by
  induction a using rec with
  | mk p =>
    induction b using rec with
    | mk q =>
      obtain ⟨r, hr⟩ := PtSimplex.MulStruct.nonempty p q (Fin.last n)
      obtain ⟨hMul⟩ := hr
      have h_eq : (π.mk p : π (n + 1) X x) * π.mk q = π.mk r :=
        hMul.mul_eq
      have hMulY :
          PtSimplex.MulStruct (PtSimplex.map f h p) (PtSimplex.map f h q)
            (PtSimplex.map f h r) (Fin.last n) :=
        { map := hMul.map ≫ f
          δ_castSucc_castSucc_map := by
            rw [← Category.assoc, hMul.δ_castSucc_castSucc_map]
            rfl
          δ_succ_castSucc_map := by
            rw [← Category.assoc, hMul.δ_succ_castSucc_map]
            rfl
          δ_succ_succ_map := by
            rw [← Category.assoc, hMul.δ_succ_succ_map]
            rfl
          δ_map_of_lt := fun j hj => by
            rw [← Category.assoc, hMul.δ_map_of_lt j hj, SSet.const_comp, h]
          δ_map_of_gt := fun j hj => by
            rw [← Category.assoc, hMul.δ_map_of_gt j hj, SSet.const_comp, h] }
      have h_eqY :
          π.mk (PtSimplex.map f h p) * π.mk (PtSimplex.map f h q) =
            π.mk (PtSimplex.map f h r) :=
        hMulY.mul_eq
      calc π.map f h (n + 1) (π.mk p * π.mk q)
          = π.map f h (n + 1) (π.mk r) := by rw [h_eq]
        _ = π.mk (PtSimplex.map f h r) := by simp [π.map_mk]
        _ = π.mk (PtSimplex.map f h p) * π.mk (PtSimplex.map f h q) := by
            rw [← h_eqY]
        _ = π.map f h (n + 1) (π.mk p) * π.map f h (n + 1) (π.mk q) := by
            simp [π.map_mk]

lemma map_one {X Y : SSet.{u}} {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (f : X ⟶ Y) (h : f.app _ x = y) (n : ℕ) :
    π.map f h n (1 : π n X x) = 1 := by
  have h1 : (1 : π n X x) =
      π.mk (RelativeMorphism.const : X.PtSimplex n x) := rfl
  have h2 : (1 : π n Y y) =
      π.mk (RelativeMorphism.const : Y.PtSimplex n y) := rfl
  calc π.map f h n (1 : π n X x)
      = π.map f h n
          (π.mk (RelativeMorphism.const : X.PtSimplex n x)) := by
        rw [h1]
    _ = π.mk (PtSimplex.map f h
          (RelativeMorphism.const : X.PtSimplex n x)) := by
        simp [π.map_mk]
    _ = π.mk (RelativeMorphism.const : Y.PtSimplex n y) := by
        congr
        apply RelativeMorphism.ext
        show RelativeMorphism.map
            (PtSimplex.map f h
              (RelativeMorphism.const : X.PtSimplex n x)) =
          RelativeMorphism.map
            (RelativeMorphism.const : Y.PtSimplex n y)
        calc RelativeMorphism.map
              (PtSimplex.map f h
                (RelativeMorphism.const : X.PtSimplex n x))
            = RelativeMorphism.map
                (RelativeMorphism.const : X.PtSimplex n x) ≫ f := rfl
          _ = SSet.const (X := Δ[n]) x ≫ f := rfl
          _ = SSet.const (X := Δ[n]) y := by
              rw [SSet.const_comp, h]
          _ = RelativeMorphism.map
                (RelativeMorphism.const : Y.PtSimplex n y) := rfl
    _ = (1 : π n Y y) := by rw [← h2]

/-- The induced multiplicative homotopy-group map in positive degree. -/
def mapHom {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (f : X ⟶ Y) (h : f.app _ x = y) (n : ℕ) :
    π (n + 1) X x →ₙ* π (n + 1) Y y where
  toFun := π.map f h (n + 1)
  map_mul' a b := map_mul f h n a b

@[simp]
lemma mapHom_apply {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (f : X ⟶ Y) (h : f.app _ x = y) (n : ℕ)
    (q : π (n + 1) X x) :
    mapHom f h n q = π.map f h (n + 1) q :=
  rfl

lemma mapHom_id {X : SSet.{u}} [KanComplex X] {x : X _⦋0⦌}
    (n : ℕ) (q : π (n + 1) X x) :
    mapHom (𝟙 X) rfl n q = q := by
  rw [mapHom_apply]
  exact map_id_apply q

lemma mapHom_comp {X Y Z : SSet.{u}} [KanComplex X] [KanComplex Y]
    [KanComplex Z] {x : X _⦋0⦌} {y : Y _⦋0⦌} {z : Z _⦋0⦌}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : f.app _ x = y) (hg : g.app _ y = z)
    (n : ℕ) (q : π (n + 1) X x) :
    mapHom (f ≫ g) (by simp [hf, hg]) n q =
      mapHom g hg n (mapHom f hf n q) := by
  simp only [mapHom_apply]
  exact π.map_comp f g hf hg q

/-- Equivalence on homotopy groups induced by an isomorphism of simplicial sets. -/
noncomputable def equivOfIso (e : X ≅ Y) (h : e.hom.app _ x = y) (n : ℕ) :
    π n X x ≃ π n Y y where
  toFun := map e.hom h n
  invFun := map e.inv (by
    calc e.inv.app _ y = e.inv.app _ (e.hom.app _ x) := by rw [h]
      _ = (e.hom ≫ e.inv).app _ x := rfl
      _ = x := by simp [e.hom_inv_id]) n
  left_inv q := by
    have hinv : e.inv.app _ y = x := by
      calc e.inv.app _ y = e.inv.app _ (e.hom.app _ x) := by rw [h]
        _ = (e.hom ≫ e.inv).app _ x := rfl
        _ = x := by simp [e.hom_inv_id]
    have hcomp : (e.hom ≫ e.inv).app _ x = x := by simp [e.hom_inv_id]
    have key : map e.inv hinv n (map e.hom h n q) = map (e.hom ≫ e.inv) hcomp n q := by
      rw [← map_comp_apply e.hom e.inv h hinv hcomp]
    rw [key]
    induction q using rec with
    | mk p =>
      simp only [map_mk]
      apply congrArg π.mk
      apply RelativeMorphism.ext
      calc RelativeMorphism.map (PtSimplex.map (e.hom ≫ e.inv) hcomp p)
          = RelativeMorphism.map p ≫ (e.hom ≫ e.inv) := rfl
        _ = RelativeMorphism.map p := by simp [e.hom_inv_id]
  right_inv q := by
    have hinv : e.inv.app _ y = x := by
      calc e.inv.app _ y = e.inv.app _ (e.hom.app _ x) := by rw [h]
        _ = (e.hom ≫ e.inv).app _ x := rfl
        _ = x := by simp [e.hom_inv_id]
    have hcomp' : (e.inv ≫ e.hom).app _ y = y := by simp [e.inv_hom_id]
    have key : map e.hom h n (map e.inv hinv n q) = map (e.inv ≫ e.hom) hcomp' n q := by
      rw [← map_comp_apply e.inv e.hom hinv h hcomp']
    rw [key]
    induction q using rec with
    | mk p =>
      simp only [map_mk]
      apply congrArg π.mk
      apply RelativeMorphism.ext
      calc RelativeMorphism.map (PtSimplex.map (e.inv ≫ e.hom) hcomp' p)
          = RelativeMorphism.map p ≫ (e.inv ≫ e.hom) := rfl
        _ = RelativeMorphism.map p := by simp [e.inv_hom_id]

@[simp]
lemma equivOfIso_apply (e : X ≅ Y) (h : e.hom.app _ x = y) (n : ℕ)
    (q : π n X x) : (equivOfIso e h n) q = map e.hom h n q :=
  rfl

end π

end KanComplex

end SSet
