/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.QuotientLineDescentModels
public import Batteries.Util.ProofWanted

/-!
# Native associated-line descent integration

The source module, group action, parameter comparison and complete
descent square are fixed native maps. No line or Picard degree is assigned
without those comparisons. Source: Stacks Project, Tag 03LF;
Ciocan-Fontanine--Kim--Maulik, arXiv:1106.3724v2, Section 2.4.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.QuotientLineDescentModelsWanted

open MathlibExt.AlgebraicGeometry MathlibExt.AlgebraicGeometry.QuotientLineDescentModels

open CategoryTheory CategoryTheory.MonObj _root_.AlgebraicGeometry
open GroupTorsorGeometry LinearizedLineBundles

def_wanted nativeAssociatedLine
    {S : Scheme.{0}} (G W : Over S) [GrpObj G] [ModObj G W]
    {T : Over S} (P : QuotientObject G W T) (E : LinearizedLineBundle G W) :
    DescendedLine G W P E

end WantedExt.AlgebraicGeometry.QuotientLineDescentModelsWanted
