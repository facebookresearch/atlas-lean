/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Comonad.CobarCosimplicial
public import MathlibExt.AlgebraicTopology.SimplicialObject.DataRev
public import MathlibExt.AlgebraicTopology.SimplicialObject.ToAugmented

/-!
# Simplicial bar resolutions of a comonad

Let `G` be a comonad on a category `C`, with counit `ε : G → Id`
and comultiplication `Δ : G → G²`. Every object `A` has a canonical
augmented simplicial bar object with degree `n` term `G^(n+1)(A)`.
For `0≤i≤n+1`, its face from degree `n+1` to `n` is
`∂_i=G^i(ε_(G^(n+1-i)(A)))`; for `0≤i≤n`, its degeneracy from
`n` to `n+1` is `σ_i=G^i(Δ_(G^(n-i)(A)))`.
In particular the degree-one faces are `ε_(GA)` and `G(ε_A)`,
and the degree-zero augmentation is `ε_A`.

The preliminary insertion order is reversed to give these standard
simplicial indices. The construction is functorial in the arbitrary
object `A`: a map `f : A → B` acts in degree `n` by `G^(n+1)(f)`
and at the augmentation point by `f`. No additional structure on
`A` is part of the construction.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, §8.6.4.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory Opposite

namespace CategoryTheory.Comonad

variable {C : Type u} [Category.{v} C]

/-- Let `C` be a category, `G` a comonad with counit `ε` and
comultiplication `Δ`, and `A : C`. For natural numbers `m,n`, the iterated powers satisfy
`G^(m+n)(A)=G^m(G^n(A))`. -/
theorem comonadPow_add_obj (G : Comonad C) (m n : ℕ) (A : C) :
    (comonadPow G (m + n)).obj A =
      (comonadPow G m).obj ((comonadPow G n).obj A) := by
  induction m generalizing A with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_add]
      change (comonadPow G (m + n)).obj (G.toFunctor.obj A) =
        (comonadPow G m).obj
          (G.toFunctor.obj ((comonadPow G n).obj A))
      rw [ih (G.toFunctor.obj A), comonadPow_obj_G_comm G n A]

/-- Let `C` be a category, `G` a comonad with counit `ε` and
comultiplication `Δ`, and `A : C`. There is simplicial data with degree-`n` object `G^(n+1)(A)`
in the preliminary insertion order: its faces are
`G^(n+1-i)(ε_(G^i(A)))` and degeneracies are
`G^(n-i)(Δ_(G^i(A)))`, with indices in the respective ranges. -/
noncomputable def resolutionRawData (G : Comonad C) (A : C) :
    SimplicialObject.Data C where
  obj n := (comonadPow G (n + 1)).obj A
  δ i := epsilonAtPos G (i := i) _ A
  σ i := deltaAtPos G _ i A
  δ_comp_δ := by
    intro n i j h
    exact (epsilonAtPos_deg_deg G (n + 1) i j h A).symm
  δ_comp_σ_of_le := by
    intro n i j h
    exact deltaAtPos_epsilonAtPos_succ_castSucc_of_le
      G (n + 1) j i h A
  δ_comp_σ_self := by
    intro n i
    exact deltaAtPos_epsilonAtPos_castSucc G (n + 1) i A
  δ_comp_σ_succ := by
    intro n i
    exact deltaAtPos_epsilonAtPos_succ G (n + 1) i A
  δ_comp_σ_of_gt := by
    intro n i j h
    exact deltaAtPos_epsilonAtPos_castSucc_succ_of_lt
      G (n + 1) j i h A
  σ_comp_σ := by
    intro n i j h
    exact (deltaAtPos_face_face G (n + 1) i j h A).symm

/-- Let `C` be a category, `G` a comonad with counit `ε` and
comultiplication `Δ`, and `A : C`. Reversing the finite face and degeneracy indices gives
simplicial data with faces `G^i(ε_(G^(n+1-i)(A)))` and degeneracies
`G^i(Δ_(G^(n-i)(A)))` on the objects `G^(n+1)(A)`. -/
noncomputable def resolutionData (G : Comonad C) (A : C) :
    SimplicialObject.Data C :=
  (resolutionRawData G A).rev

@[simp]
theorem resolutionData_obj (G : Comonad C) (A : C) (n : ℕ) :
    (resolutionData G A).obj n = (comonadPow G (n + 1)).obj A :=
  rfl

/-- Let `C` be a category, `G` a comonad with counit `ε` and
comultiplication `Δ`, and `A : C`. For `i : Fin(n+2)`, the face of the bar data from
`G^(n+2)(A)` to `G^(n+1)(A)` is
`∂_i=G^i(ε_(G^(n+1-i)(A)))`, under the iterated-power identifications. -/
@[simp]
theorem resolutionData_δ (G : Comonad C) (A : C) {n : ℕ}
    (i : Fin (n + 2)) :
    (resolutionData G A).δ i = cobarEpsilonAtPos G (n + 1) i A :=
  rfl

/-- Let `C` be a category, `G` a comonad with counit `ε` and
comultiplication `Δ`, and `A : C`. For `i : Fin(n+1)`, the degeneracy of the bar data from
`G^(n+1)(A)` to `G^(n+2)(A)` is
`σ_i=G^i(Δ_(G^(n-i)(A)))`, under the iterated-power identifications. -/
@[simp]
theorem resolutionData_σ (G : Comonad C) (A : C) {n : ℕ}
    (i : Fin (n + 1)) :
    (resolutionData G A).σ i = cobarDeltaAtPos G (n + 1) i A :=
  rfl

/-- Let `C` be a category, `G` a comonad with counit `ε` and
comultiplication `Δ`, and `A : C`. The standard bar data define a simplicial object with
terms `G^(n+1)(A)`, counit-insertion faces, and comultiplication-
insertion degeneracies in the stated order. -/
noncomputable def resolutionBar (G : Comonad C) (A : C) :
    SimplicialObject C :=
  (resolutionData G A).toSimplicialObject

@[simp]
theorem resolutionBar_obj (G : Comonad C) (A : C) (n : ℕ) :
    (resolutionBar G A).obj (op (SimplexCategory.mk n)) =
      (comonadPow G (n + 1)).obj A :=
  rfl

/-- Let `C` be a category, `G` a comonad with counit `ε` and
comultiplication `Δ`, and `A : C`. Each degree-`n` term of the simplicial bar has its
canonical level isomorphism to `G^(n+1)(A)`. -/
noncomputable def resolutionBarObjIso (G : Comonad C) (A : C) (n : ℕ) :
    (resolutionBar G A).obj (op (SimplexCategory.mk n)) ≅
      (comonadPow G (n + 1)).obj A := by
  change (comonadPow G (n + 1)).obj A ≅
    (comonadPow G (n + 1)).obj A
  exact Iso.refl _

/-- Let `C` be a category, `G` a comonad with counit `ε` and
comultiplication `Δ`, and `A : C`. For `i : Fin(n+2)`, the simplicial map of the face
`[n] → [n+1]` is the counit insertion
`G^i(ε_(G^(n+1-i)(A))) : G^(n+2)(A) → G^(n+1)(A)`. -/
@[simp]
theorem resolutionBar_map_δ_op (G : Comonad C) (A : C) {n : ℕ}
    (i : Fin (n + 2)) :
    (resolutionBar G A).map (SimplexCategory.δ i).op =
      cobarEpsilonAtPos G (n + 1) i A := by
  exact SimplicialObject.Data.toSimplicialObject_map_δ
    (resolutionData G A) i

/-- Let `C` be a category, `G` a comonad with counit `ε` and
comultiplication `Δ`, and `A : C`. For `i : Fin(n+1)`, the simplicial degeneracy from degree
`n` to `n+1` is
`G^i(Δ_(G^(n-i)(A))) : G^(n+1)(A) → G^(n+2)(A)`. -/
@[simp]
theorem resolutionBar_map_σ_op (G : Comonad C) (A : C) {n : ℕ}
    (i : Fin (n + 1)) :
    (resolutionBar G A).map (SimplexCategory.σ i).op =
      cobarDeltaAtPos G (n + 1) i A := by
  exact SimplicialObject.Data.toSimplicialObject_map_σ
    (resolutionData G A) i

/-- Let `C` be a category, `G` a comonad with counit `ε` and
comultiplication `Δ`, and `A : C`. For every face index `i : Fin(n+2)`, the level
isomorphisms from bar degrees `n+1,n` to `G^(n+2)(A),G^(n+1)(A)`
intertwine that simplicial face with its counit insertion. -/
@[reassoc]
theorem resolutionBarObjIso_hom_face (G : Comonad C) (A : C)
    (n : ℕ) (i : Fin (n + 2)) :
    (resolutionBarObjIso G A (n + 1)).hom ≫
        cobarEpsilonAtPos G (n + 1) i A =
      (resolutionBar G A).map (SimplexCategory.δ i).op ≫
        (resolutionBarObjIso G A n).hom := by
  rw [resolutionBar_map_δ_op]
  simp [resolutionBarObjIso]

/-- Let `C` be a category, `G` a comonad with counit `ε` and
comultiplication `Δ`, and `A : C`. For every degeneracy index `i : Fin(n+1)`, the level
isomorphisms from bar degrees `n,n+1` intertwine that simplicial
degeneracy with its comultiplication insertion. -/
@[reassoc]
theorem resolutionBarObjIso_hom_degeneracy (G : Comonad C) (A : C)
    (n : ℕ) (i : Fin (n + 1)) :
    (resolutionBarObjIso G A n).hom ≫
        cobarDeltaAtPos G (n + 1) i A =
      (resolutionBar G A).map (SimplexCategory.σ i).op ≫
        (resolutionBarObjIso G A (n + 1)).hom := by
  rw [resolutionBar_map_σ_op]
  simp [resolutionBarObjIso]

/-- Let `C` be a category, `G` a comonad with counit `ε` and
comultiplication `Δ`, and `A : C`. The zeroth face from bar degree one to zero is
`ε_(G(A)) : G²(A) → G(A)`. -/
theorem resolutionBar_face_zero_degree_one (G : Comonad C) (A : C) :
    (resolutionBar G A).map
      (SimplexCategory.δ (0 : Fin 2)).op =
        G.ε.app (G.toFunctor.obj A) := by
  rw [resolutionBar_map_δ_op]
  rfl

/-- Let `C` be a category, `G` a comonad with counit `ε` and
comultiplication `Δ`, and `A : C`. The first face from bar degree one to zero is
`G(ε_A) : G²(A) → G(A)`. -/
theorem resolutionBar_face_one_degree_one (G : Comonad C) (A : C) :
    (resolutionBar G A).map
      (SimplexCategory.δ (1 : Fin 2)).op =
        G.toFunctor.map (G.ε.app A) := by
  rw [resolutionBar_map_δ_op]
  rfl

/-- Let `C` be a category, `G` a comonad with counit `ε` and
comultiplication `Δ`, and `A : C`. The only degeneracy from degree zero to one is the
comultiplication `Δ_A : G(A) → G²(A)`. -/
theorem resolutionBar_degeneracy_zero (G : Comonad C) (A : C) :
    (resolutionBar G A).map
      (SimplexCategory.σ (0 : Fin 1)).op = G.δ.app A := by
  rw [resolutionBar_map_σ_op]
  rfl

/-- Let `C` be a category, `G` a comonad with counit `ε` and
comultiplication `Δ`, and `A : C`. The augmentation `ε_A : G(A) → A` equalizes the two
 degree-one faces:
`ε_(GA) ≫ ε_A = G(ε_A) ≫ ε_A`. -/
theorem resolutionData_counit_isBalanced (G : Comonad C) (A : C) :
    SimplicialObject.Data.IsBalanced
      (X := resolutionData G A) (G.ε.app A) := by
  change G.ε.app (G.toFunctor.obj A) ≫ G.ε.app A =
    G.toFunctor.map (G.ε.app A) ≫ G.ε.app A
  exact (G.ε.naturality (G.ε.app A)).symm

/-- Let `C` be a category, `G` a comonad with counit `ε` and
comultiplication `Δ`, and `A : C`. The bar simplicial data augmented at `A` by
`ε_A : G(A) → A` form augmented simplicial data. -/
noncomputable def resolutionAugmentedData (G : Comonad C) (A : C) :
    SimplicialObject.Data.Augmented C :=
  SimplicialObject.Data.Augmented.augment
    (resolutionData G A) A (G.ε.app A)
      (resolutionData_counit_isBalanced G A)

/-- Let `C` be a category, `G` a comonad with counit `ε` and
comultiplication `Δ`, and `f : A → B` a morphism of objects in `C`. Applying `G^(n+1)` to `f` in each degree gives a map
between the preliminary bar data, compatible with every counit
and comultiplication insertion. -/
noncomputable def resolutionRawHom (G : Comonad C) {A B : C}
    (f : A ⟶ B) : resolutionRawData G A ⟶ resolutionRawData G B where
  app n := (comonadPow G (n + 1)).map f
  w_δ i := epsilonAtPos_naturality G _ i f
  w_σ i := deltaAtPos_naturality G _ i f

/-- Let `C` be a category, `G` a comonad with counit `ε` and
comultiplication `Δ`, and `f : A → B` a morphism of objects in `C`. The degreewise maps `G^(n+1)(f)` give a morphism of
standard-indexed bar data, commuting with all faces and degeneracies. -/
noncomputable def resolutionDataHom (G : Comonad C) {A B : C}
    (f : A ⟶ B) : resolutionData G A ⟶ resolutionData G B :=
  SimplicialObject.Data.revHom (resolutionRawHom G f)

@[simp]
theorem resolutionDataHom_app (G : Comonad C) {A B : C}
    (f : A ⟶ B) (n : ℕ) :
    (resolutionDataHom G f).app n = (comonadPow G (n + 1)).map f :=
  rfl

@[simp]
theorem resolutionDataHom_id (G : Comonad C) (A : C) :
    resolutionDataHom G (𝟙 A) = 𝟙 (resolutionData G A) := by
  apply SimplicialObject.Data.Hom.ext
  intro n
  simp

theorem resolutionDataHom_comp (G : Comonad C) {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D) :
    resolutionDataHom G (f ≫ g) =
      resolutionDataHom G f ≫ resolutionDataHom G g := by
  apply SimplicialObject.Data.Hom.ext
  intro n
  simp

/-- Let `C` be a category, `G` a comonad with counit `ε` and
comultiplication `Δ`, and `f : A → B` a morphism of objects in `C`. The standard bar-data map extends to augmented data with
point map `f` and degree-`n` map `G^(n+1)(f)`, commuting with
`ε_A,ε_B`. -/
noncomputable def resolutionAugmentedDataHom (G : Comonad C) {A B : C}
    (f : A ⟶ B) :
    resolutionAugmentedData G A ⟶ resolutionAugmentedData G B where
  left := resolutionDataHom G f
  right := f
  w := by
    apply SimplicialObject.Data.hom_eq_of_app_zero_eq
    change G.toFunctor.map f ≫ G.ε.app B = G.ε.app A ≫ f
    exact G.ε.naturality f

@[simp]
theorem resolutionAugmentedDataHom_id (G : Comonad C) (A : C) :
    resolutionAugmentedDataHom G (𝟙 A) =
      𝟙 (resolutionAugmentedData G A) := by
  apply Comma.hom_ext
  · exact resolutionDataHom_id G A
  · rfl

theorem resolutionAugmentedDataHom_comp (G : Comonad C) {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D) :
    resolutionAugmentedDataHom G (f ≫ g) =
      resolutionAugmentedDataHom G f ≫
        resolutionAugmentedDataHom G g := by
  apply Comma.hom_ext
  · exact resolutionDataHom_comp G f g
  · rfl

/-- For a comonad `G` on a category `C`, the augmented bar-data
construction is a functor of the object `A`: objects are augmented
by `ε_A`, and morphisms act by `G^(n+1)(f)` and the point map `f`. -/
noncomputable def resolutionAugmentedDataFunctor (G : Comonad C) :
    C ⥤ SimplicialObject.Data.Augmented C where
  obj A := resolutionAugmentedData G A
  map f := resolutionAugmentedDataHom G f
  map_id A := resolutionAugmentedDataHom_id G A
  map_comp f g := resolutionAugmentedDataHom_comp G f g

/-- For a comonad `G` on a category `C`, the bar construction gives
a functor `C → SimplicialObject.Augmented C`, taking `A` to its
bar object augmented by the counit and maps to their iterated-power
simplicial maps. -/
noncomputable def resolutionAugmentedFunctor (G : Comonad C) :
    C ⥤ SimplicialObject.Augmented C :=
  resolutionAugmentedDataFunctor G ⋙
    SimplicialObject.Data.Augmented.toSimplicialFunctor

/-- Let `C` be a category, `G` a comonad with counit `ε` and
comultiplication `Δ`, and `A : C`. The canonical augmented simplicial resolution of `A`
has underlying bar object `G^(n+1)(A)` and augmentation induced
by `ε_A`. -/
noncomputable def resolutionAugmented (G : Comonad C) (A : C) :
    SimplicialObject.Augmented C :=
  (resolutionAugmentedFunctor G).obj A

@[simp]
theorem resolutionAugmented_point (G : Comonad C) (A : C) :
    (resolutionAugmented G A).right = A := by
  unfold resolutionAugmented resolutionAugmentedFunctor
  exact SimplicialObject.Data.Augmented.toSimplicialFunctor_obj_right
    (resolutionAugmentedData G A)

@[simp]
theorem resolutionAugmented_left (G : Comonad C) (A : C) :
    (resolutionAugmented G A).left = resolutionBar G A := by
  unfold resolutionAugmented resolutionAugmentedFunctor resolutionBar
  exact SimplicialObject.Data.Augmented.toSimplicialFunctor_obj_left
    (resolutionAugmentedData G A)

/-- Let `C` be a category, `G` a comonad with counit `ε` and
comultiplication `Δ`, and `A : C`. The degree-zero component of the augmented bar map
`Bar_G(A) → const(A)` is the counit `ε_A : G(A) → A`. -/
@[simp]
theorem resolutionAugmented_hom_zero (G : Comonad C) (A : C) :
    (resolutionAugmented G A).hom.app
      (op (SimplexCategory.mk 0)) = G.ε.app A := by
  unfold resolutionAugmented resolutionAugmentedFunctor
  change (SimplicialObject.Data.Augmented.toSimplicialFunctor.obj
    (resolutionAugmentedData G A)).hom.app
      (op (SimplexCategory.mk 0)) = G.ε.app A
  rw [SimplicialObject.Data.Augmented.toSimplicialFunctor_obj_hom]
  exact SimplicialObject.Data.Augmented.toSimplicialAugmented_hom_app_mk
    (resolutionAugmentedData G A) 0

/-- Let `C` be a category, `G` a comonad with counit `ε` and
comultiplication `Δ`, and `f : A → B` a morphism of objects in `C`. The augmented bar functor sends `f` to the resolution
map whose degree-`n` component is `G^(n+1)(f)` and whose
augmentation-point component is `f`. -/
noncomputable def resolutionHom (G : Comonad C) {A B : C} (f : A ⟶ B) :
    resolutionAugmented G A ⟶ resolutionAugmented G B :=
  (resolutionAugmentedFunctor G).map f

@[simp]
theorem resolutionAugmentedFunctor_obj (G : Comonad C) (A : C) :
    (resolutionAugmentedFunctor G).obj A = resolutionAugmented G A :=
  rfl

@[simp]
theorem resolutionAugmentedFunctor_map (G : Comonad C) {A B : C}
    (f : A ⟶ B) :
    (resolutionAugmentedFunctor G).map f = resolutionHom G f :=
  rfl

@[simp]
theorem resolutionHom_id (G : Comonad C) (A : C) :
    resolutionHom G (𝟙 A) = 𝟙 (resolutionAugmented G A) :=
  (resolutionAugmentedFunctor G).map_id A

theorem resolutionHom_comp (G : Comonad C) {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D) :
    resolutionHom G f ≫ resolutionHom G g = resolutionHom G (f ≫ g) :=
  ((resolutionAugmentedFunctor G).map_comp f g).symm

/-- Let `C` be a category, `G` a comonad with counit `ε` and
comultiplication `Δ`, and `f : A → B` a morphism of objects in `C`. The simplicial component of the augmented resolution map
in degree `n` is `G^(n+1)(f)`. -/
@[simp]
theorem resolutionHom_left_app (G : Comonad C) {A B : C}
    (f : A ⟶ B) (n : ℕ) :
    (resolutionHom G f).left.app (op (SimplexCategory.mk n)) =
      (comonadPow G (n + 1)).map f :=
  rfl

/-- Let `C` be a category, `G` a comonad with counit `ε` and
comultiplication `Δ`, and `f : A → B` a morphism of objects in `C`. The component at the augmentation point of the comonad
bar resolution map is `f : A → B`. -/
@[simp]
theorem resolutionHom_right (G : Comonad C) {A B : C} (f : A ⟶ B) :
    (resolutionHom G f).right = f :=
  rfl

end CategoryTheory.Comonad

end
