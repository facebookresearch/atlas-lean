/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.StackFirstChernSchemeComparison

/-!
A supposed zero section cannot represent a nonzero module element, even
through an isomorphism of affine stack points. This catches a translated
zero section which agrees only on the underlying bundle projection.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open StackCycleGeometry StackAffineModules StackVectorBundles StackFirstChernOperators

example {S : Scheme.{0}} {X : Stack S} (E : VectorBundle X)
    (a : AffinePoint X) (m : E.module.val.presheaf.obj (op a)) (nonzero : m ≠ 0) :
    ¬ Nonempty ((zeroElements E).obj a ≅
      op ((sectionPresheaf E.module.val).elementsMk (op a) m)) := by
  rintro ⟨e⟩
  have h := e.inv.unop.map_val
  change E.module.val.presheaf.presheaf.map e.inv.unop.hom 0 = m at h
  rw [map_zero] at h
  exact nonzero h.symm

example {S : Scheme.{0}} {X : Stack S} (E : VectorBundle X)
    (a : AffinePoint X) [Nontrivial ((rings X).obj (op a))]
    (frame : E.module.val.presheaf.obj (op a) ≃ₗ[(rings X).obj (op a)] (rings X).obj (op a)) :
    ¬ Nonempty ((zeroElements E).obj a ≅
      op ((sectionPresheaf E.module.val).elementsMk (op a) (frame.symm 1))) := by
  rintro ⟨e⟩
  have h := e.inv.unop.map_val
  change E.module.val.presheaf.presheaf.map e.inv.unop.hom 0 = frame.symm 1 at h
  rw [map_zero] at h
  have hh := congrArg frame h
  simp at hh
