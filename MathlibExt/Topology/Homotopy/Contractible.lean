/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Homotopy.Contractible

/-!
# Homotopies and equivalences involving contractible spaces

Any two continuous maps into a contractible space are homotopic. The file also
gives invariance and cancellation laws for nullhomotopy and constructs a
homotopy equivalence with a specified forward map between contractible spaces.
-/

@[expose] public section

universe u v w

open ContinuousMap

namespace ContinuousMap

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Any two continuous maps into a contractible space are homotopic.
Uses `id_nullhomotopic` and composition of homotopies. -/
theorem homotopic_of_contractible_codomain [ContractibleSpace Y] (f g : C(X, Y)) :
    Homotopic f g := by
  obtain ⟨y₀, hy₀⟩ := id_nullhomotopic Y
  have hf : Homotopic f (ContinuousMap.const X y₀) := by simpa using hy₀.comp (.refl f)
  have hg : Homotopic g (ContinuousMap.const X y₀) := by simpa using hy₀.comp (.refl g)
  exact hf.trans hg.symm

/-- Nullhomotopy is invariant under homotopy of the underlying map. -/
theorem Nullhomotopic.of_homotopic {f g : C(X, Y)}
    (hf : f.Nullhomotopic) (hfg : Homotopic f g) :
    g.Nullhomotopic := by
  obtain ⟨y, hy⟩ := hf
  exact ⟨y, hfg.symm.trans hy⟩

/-- All values of a nullhomotopic map lie in one path component. -/
theorem Nullhomotopic.joined_apply (f : C(X, Y))
    (hf : f.Nullhomotopic) (x₀ x₁ : X) :
    Joined (f x₀) (f x₁) := by
  obtain ⟨y, ⟨H⟩⟩ := hf
  exact ⟨(H.evalAt x₀).trans (H.evalAt x₁).symm⟩

/-- A map is nullhomotopic if its precomposition by the forward map of a
homotopy equivalence is nullhomotopic. -/
theorem Nullhomotopic.cancel_precomp_homotopyEquiv
    (e : X ≃ₕ Y) (q : C(Y, Z))
    (h : (q.comp e.toFun).Nullhomotopic) :
    q.Nullhomotopic := by
  have hpre : ((q.comp e.toFun).comp e.invFun).Nullhomotopic :=
    h.comp_left e.invFun
  apply hpre.of_homotopic
  have hq :
      Homotopic (q.comp (e.toFun.comp e.invFun))
        (q.comp (ContinuousMap.id Y)) :=
    Homotopic.comp (Homotopic.refl q) e.right_inv
  simpa only [ContinuousMap.comp_assoc, ContinuousMap.comp_id] using hq

end ContinuousMap

namespace ContinuousMap.HomotopyEquiv

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A specified continuous map between contractible spaces extends to a
homotopy equivalence whose forward map is definitionally `f`. The inverse is a
constant map; contractibility gives nonemptiness. Inverse laws follow from
`ContinuousMap.homotopic_of_contractible_codomain`. -/
noncomputable def ofContractible [ContractibleSpace X] [ContractibleSpace Y]
    (f : C(X, Y)) : X ≃ₕ Y :=
  let x₀ : X := (id_nullhomotopic X).choose
  { toFun := f
    invFun := ContinuousMap.const Y x₀
    left_inv := by
      simpa using
        homotopic_of_contractible_codomain (ContinuousMap.const X x₀)
          (ContinuousMap.id X)
    right_inv := by
      simpa using
        homotopic_of_contractible_codomain (ContinuousMap.const Y (f x₀))
          (ContinuousMap.id Y)
  }

/-- The `toFun` projection of `ofContractible f` is definitionally `f`. -/
@[simp]
theorem ofContractible_toFun [ContractibleSpace X] [ContractibleSpace Y]
    (f : C(X, Y)) : (ofContractible f).toFun = f :=
  rfl

end ContinuousMap.HomotopyEquiv
