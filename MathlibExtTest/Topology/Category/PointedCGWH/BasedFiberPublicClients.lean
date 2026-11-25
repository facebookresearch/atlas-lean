/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/

import MathlibExt.Topology.Category.PointedCGWH.BasedFiber

/-!
# Clients of the pointed strict-fiber foundation alone

Both original pointed functions are available without any contraction,
loop, mapping-path fiber, or model-category import. The actual total and
point projections, identity square, and composed squares retain the given
basepoints and lifts at arbitrary native universe combinations.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CGWH.limits

namespace PointedCGWH.BasedFiberPublicClients

example {E B : CGWH.{u, v}} (p : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) (e : CGWH.point.{u, v} ⟶ E)
    (over : e ≫ p = b) :
    (strictFiberPointed p b e over).hom = CGWH.strictFiberPoint p b e over := rfl

example {E B E' B' : CGWH.{u, v}}
    {p : E ⟶ B} {b : CGWH.point.{u, v} ⟶ B}
    {e : CGWH.point.{u, v} ⟶ E} (over : e ≫ p = b)
    {p' : E' ⟶ B'} {b' : CGWH.point.{u, v} ⟶ B'}
    {e' : CGWH.point.{u, v} ⟶ E'} (over' : e' ≫ p' = b')
    (a : E ⟶ E') (d : B ⟶ B')
    (square : a ≫ p' = p ≫ d) (base : b ≫ d = b') (point : e ≫ a = e') :
    (strictFiberPointedMap over over' a d square base point).right =
      CGWH.strictFiberMap a d square base := rfl

example {E B E' B' : CGWH.{u, v}}
    {p : E ⟶ B} {b : CGWH.point.{u, v} ⟶ B}
    {e : CGWH.point.{u, v} ⟶ E} (over : e ≫ p = b)
    {p' : E' ⟶ B'} {b' : CGWH.point.{u, v} ⟶ B'}
    {e' : CGWH.point.{u, v} ⟶ E'} (over' : e' ≫ p' = b')
    (a : E ⟶ E') (d : B ⟶ B')
    (square : a ≫ p' = p ≫ d) (base : b ≫ d = b') (point : e ≫ a = e') :
    (strictFiberPointedMap over over' a d square base point).right ≫
        CGWH.strictFiberToTotal p' b' = CGWH.strictFiberToTotal p b ≫ a ∧
      (strictFiberPointedMap over over' a d square base point).right ≫
        CGWH.strictFiberToPoint p' b' = CGWH.strictFiberToPoint p b :=
  ⟨CGWH.strictFiberMap_toTotal a d square base,
    CGWH.strictFiberMap_toPoint a d square base⟩

example {E B E' B' : CGWH.{u, v}}
    {p : E ⟶ B} {b : CGWH.point.{u, v} ⟶ B}
    {e : CGWH.point.{u, v} ⟶ E} (over : e ≫ p = b)
    {p' : E' ⟶ B'} {b' : CGWH.point.{u, v} ⟶ B'}
    {e' : CGWH.point.{u, v} ⟶ E'} (over' : e' ≫ p' = b')
    (a : E ⟶ E') (d : B ⟶ B')
    (square : a ≫ p' = p ≫ d) (base : b ≫ d = b') (point : e ≫ a = e') :
    (strictFiberPointed p b e over).hom ≫
        (strictFiberPointedMap over over' a d square base point).right =
      (strictFiberPointed p' b' e' over').hom :=
  Under.w (strictFiberPointedMap over over' a d square base point)

example {E B : CGWH.{u, v}} (p : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) (e : CGWH.point.{u, v} ⟶ E)
    (over : e ≫ p = b) :
    strictFiberPointedMap over over (𝟙 E) (𝟙 B)
        (by simp) (by simp) (by simp) = 𝟙 (strictFiberPointed p b e over) := by
  apply Under.UnderMorphism.ext
  exact CGWH.strictFiberMap_id p b

example {E B E' B' E'' B'' : CGWH.{u, v}}
    {p : E ⟶ B} {b : CGWH.point.{u, v} ⟶ B}
    {e : CGWH.point.{u, v} ⟶ E} (over : e ≫ p = b)
    {p' : E' ⟶ B'} {b' : CGWH.point.{u, v} ⟶ B'}
    {e' : CGWH.point.{u, v} ⟶ E'} (over' : e' ≫ p' = b')
    {p'' : E'' ⟶ B''} {b'' : CGWH.point.{u, v} ⟶ B''}
    {e'' : CGWH.point.{u, v} ⟶ E''} (over'' : e'' ≫ p'' = b'')
    (a₁ : E ⟶ E') (d₁ : B ⟶ B')
    (square₁ : a₁ ≫ p' = p ≫ d₁) (base₁ : b ≫ d₁ = b') (point₁ : e ≫ a₁ = e')
    (a₂ : E' ⟶ E'') (d₂ : B' ⟶ B'')
    (square₂ : a₂ ≫ p'' = p' ≫ d₂) (base₂ : b' ≫ d₂ = b'') (point₂ : e' ≫ a₂ = e'') :
    strictFiberPointedMap over over' a₁ d₁ square₁ base₁ point₁ ≫
        strictFiberPointedMap over' over'' a₂ d₂ square₂ base₂ point₂ =
      strictFiberPointedMap over over'' (a₁ ≫ a₂) (d₁ ≫ d₂)
        (by rw [Category.assoc, square₂, ← Category.assoc, square₁, Category.assoc])
        (by rw [← Category.assoc, base₁, base₂])
        (by rw [← Category.assoc, point₁, point₂]) := by
  apply Under.UnderMorphism.ext
  exact CGWH.strictFiberMap_comp a₁ d₁ square₁ base₁ a₂ d₂ square₂ base₂

example {E B : CGWH.{u, 0}} (p : E ⟶ B)
    (b : CGWH.point.{u, 0} ⟶ B) (e : CGWH.point.{u, 0} ⟶ E)
    (over : e ≫ p = b) : PointedCGWH.{u, 0} := strictFiberPointed p b e over

example {E B : CGWH.{0, v}} (p : E ⟶ B)
    (b : CGWH.point.{0, v} ⟶ B) (e : CGWH.point.{0, v} ⟶ E)
    (over : e ≫ p = b) : PointedCGWH.{0, v} := strictFiberPointed p b e over

end PointedCGWH.BasedFiberPublicClients
