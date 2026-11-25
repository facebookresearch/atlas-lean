/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.CategoryTheory.DGModelContracts
public import MathlibExt.CategoryTheory.DGQuasiFunctorModels

/-!
# Normalized DG replacement and tensor construction providers

Completed DG/H0/Yoneda/ordinary tensor primitives are source ports, not
Wanted requests. The requests below construct models on those exact
objects, with Hom quasi-isomorphisms, actual lifting properties and
generator-normalized localized tensor maps. They do not assume an
internal-Hom equivalence or a moduli geometricity conclusion.

Source: Toën, arXiv:math/0408337v7, §§2--3 and §6. The separate
source-normalized module/trace/mapping comparisons retain their own
endpoints; ordinary module-derived and spectral invariants are not
identified merely by a matching name.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.DGModelContractsWanted

open _root_.CategoryTheory
open MathlibExt.CategoryTheory.DGModelContracts

universe u

def_wanted dg_cofibrant_replacement_functor (k : Type u) [CommRing k] :
    ReplacementFunctor k

def_wanted dg_tensor_map (k : Type u) [CommRing k]
    (A B C D : DGCat k) (f : A ⟶ B) (g : C ⟶ D) : TensorMapModel f g

def_wanted dg_localized_tensor (k : Type u) [CommRing k]
    (Q : ReplacementFunctor k) (C : DGCat k) : LocalizedTensorModel Q C

end WantedExt.AlgebraicGeometry.DGModelContractsWanted
