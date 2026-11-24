/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GroupTorsorGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Batteries.Util.ProofWanted

/-!
# Native torsor and associated-bundle integration requests

Each request fixes actual scheme projections, actions, fibre products,
quotient maps and graph sections. These are native carrier integrations
of fppf torsor/descent constructions, not new abstract torsor or GIT
existence claims. AxiomMath/Stacks at the cited revision already
implements the corresponding fppf torsor categories and comparisons;
the source normalization is retained in these native result types.

References: Stacks Project, Tags 04UR and 0CQJ; Ciocan-Fontanine--Kim--
Maulik, arXiv:1106.3724v2, Section 2.4.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.GroupTorsorGeometryWanted

open MathlibExt.AlgebraicGeometry MathlibExt.AlgebraicGeometry.GroupTorsorGeometry

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonObj _root_.AlgebraicGeometry

def_wanted nativeTorsorReindex
    {S : Scheme.{0}} (G : Over S) [GrpObj G]
    {T T' : Over S} (P : Torsor G T) (f : T' ⟶ T) : Reindex G P f

def_wanted nativeAssociatedBundle
    {S : Scheme.{0}} (G W : Over S) [GrpObj G] [ModObj G W]
    [IsAffineHom G.hom] [IsAffineHom W.hom]
    {T : Over S} (P : QuotientObject G W T) : AssociatedBundle G W P

def_wanted nativeAssociatedReindex
    {S : Scheme.{0}} (G W : Over S) [GrpObj G] [ModObj G W]
    [IsAffineHom G.hom] [IsAffineHom W.hom]
    {T T' : Over S} (P : QuotientObject G W T) (f : T' ⟶ T)
    (R : Reindex G P.torsor f) (B : AssociatedBundle G W P)
    (B' : AssociatedBundle G W (reindexObject G W P f R)) : AssociatedReindex G W P f R B B'

end WantedExt.AlgebraicGeometry.GroupTorsorGeometryWanted
