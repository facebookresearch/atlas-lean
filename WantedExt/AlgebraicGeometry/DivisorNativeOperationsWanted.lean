/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.DivisorNativeOperations

/-!
# Actual divisor tensor and inverse-image realization

The objects, tensor/sections, scheme pullback, all module arrows,
unitors, associator, symmetry and inverse-image unit/tensor maps are
fixed native operations in MathlibExt. Only their line/section landing
proofs and the native symmetric monoidal coherence realization remain.
This request has no parabolic or infinite-root equivalence as an input.

Source: Borne–Vistoli arXiv:1001.0466v2, Definition3.1.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.DivisorNativeOperations

open MathlibExt.AlgebraicGeometry.DivisorNativeOperations

/-- **Tensor products and pullbacks of line bundles with sections.** For a scheme $X$, let
`DivisorObject X` be the groupoid of line bundles on $X$ with a section, with section-preserving
isomorphisms (Borne–Vistoli, Definition 3.1). The data consist of: the facts that tensor products
of such line bundles, and their pullbacks along morphisms of schemes, are line bundles, and that
the canonical map from the pullback of the structure sheaf to the structure sheaf is an
isomorphism (`Landing`); the facts that the unitors, symmetry and associator of tensor products of
modules, and the comparisons of pullback with tensor products, preserve the sections
(`Coherence`); and (`Realization`) for every scheme $X$ a symmetric monoidal structure on
`DivisorObject X` whose tensor product, unit, unitors, associator and symmetry are the tensor
product of modules with the tensor product of the sections, the structure sheaf with its unit
section, and these module isomorphisms, and for every morphism $f$ of schemes a monoidal structure
on pullback along $f$ whose unit and tensor maps are the canonical ones, with pullback along
identities and along composites identified through the corresponding isomorphisms of module
pullbacks. -/
public def_wanted nativeDivisors : NativeDivisors

end WantedExt.AlgebraicGeometry.DivisorNativeOperations
