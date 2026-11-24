/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/

import MathlibExt.Algebra.Category.Grp.FilteredKernelRepresentatives

set_option autoImplicit false
noncomputable section
universe v

open CategoryTheory CategoryTheory.Limits

namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluingTest

/-- The caller's actual original group cocones retain a genuine later null representative. -/
theorem actual_original_caller_group_cocone_kernel
    {D E : ℕ ⥤ GrpCat.{v}} (c : Cocone D) (d : Cocone E)
    (hc : IsColimit c) (hd : IsColimit d) (a : D ⟶ E) (f : c.pt ⟶ d.pt)
    (hf : ∀ n, c.ι.app n ≫ f = a.app n ≫ d.ι.app n)
    (x : c.pt) (hx : f.hom x = 1) :
    ∃ (n m : ℕ) (h : n ≤ m) (b : D.obj n),
      (c.ι.app n).hom b = x ∧ (E.map (homOfLE h)).hom ((a.app n).hom b) = 1 :=
  CategoryTheory.Limits.originalNatGroupCocone_kernel_stage c d hc hd a f hf x hx

/-- All original caller group kernels retain their literal representative past any stage bound. -/
theorem actual_original_caller_group_kernel_later_stage
    {D E : ℕ ⥤ GrpCat.{v}} (c : Cocone D) (d : Cocone E)
    (hc : IsColimit c) (hd : IsColimit d) (a : D ⟶ E) (f : c.pt ⟶ d.pt)
    (hf : ∀ n, c.ι.app n ≫ f = a.app n ≫ d.ι.app n)
    (x : c.pt) (hx : f.hom x = 1) (n₀ : ℕ) :
    ∃ (m : ℕ), n₀ ≤ m ∧ ∃ b : D.obj m,
      (c.ι.app m).hom b = x ∧ (a.app m).hom b = 1 :=
  CategoryTheory.Limits.originalNatGroupCocone_kernel_later_stage c d hc hd a f hf x hx n₀


end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluingTest
