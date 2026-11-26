/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.NisnevichTransferModels
public import MathlibExt.AlgebraicGeometry.MotivicStandardSchemes
public import MathlibExt.AlgebraicGeometry.FiniteTransfersMotivicNisnevichHasSheafification

/-!
# Wanted finite-transfer geometry, Nisnevich sheafification and standard motivic schemes

Every support, local Tor module, generic length, residue degree, coordinate
ring and source map is fixed in the public definitions. These requests
construct the corresponding genuine geometry and category structures.
The theorem `motivic_nisnevich_has_sheafification` is proved in
`MathlibExt.AlgebraicGeometry.FiniteTransfersMotivicNisnevichHasSheafification`.
No Tate representability or motivic operation theorem is assumed here.

Sources: Mazza--Voevodsky--Weibel, Lectures 1--3 and 13;
Voevodsky, arXiv:math/0107109v1, §2.
-/

open CategoryTheory
open MathlibExt.AlgebraicGeometry.FiniteTransferCycleModels
open MathlibExt.AlgebraicGeometry.FiniteTransferProductModels
open MathlibExt.AlgebraicGeometry.NisnevichTransferModels
open MathlibExt.AlgebraicGeometry.MotivicStandardSchemes

/-- The projection from the actual proper intersection is normalized on both source-product coordinates. -/
def_wanted finite_correspondence_projection (k : Type) [Field k]
    (U X Y : SmoothScheme k) (g : Generator U X) (h : Generator X Y) : CompositionProjection g h

/-- The actual Tor/residue-degree kernel has bounded finite-length generic Tor and finite image supports. -/
def_wanted finite_correspondence_intersection (k : Type) [Field k]
    (U X Y : SmoothScheme k) (g : Generator U X) (h : Generator X Y) : CompositionGeometry g h

def_wanted finite_correspondence_composition_system (k : Type) [Field k] : CompositionSystem k

/-- All components of an actual scheme graph give its integral transfer cycle. -/
def_wanted finite_correspondence_graph (k : Type) [Field k]
    (U X : SmoothScheme k) (f : U ⟶ X) : GraphGeometry f

def_wanted finite_correspondence_graph_system (k : Type) [Field k] : GraphSystem k

/-- Category laws concern the fixed Tor/residue-degree composition and the actual graph cycles. -/
theorem_wanted finite_correspondence_category_laws (k : Type) [Field k]
    (D : CompositionSystem k) (G : GraphSystem k) : CorrespondenceLaws D G

/-- The additive structure is required to use exactly the integral coefficient operations. -/
def_wanted finite_correspondence_additivity (k : Type) [Field k]
    (D : CompositionSystem k) (G : GraphSystem k) [CorrespondenceLaws D G] : CorrespondenceAdditivity D G

def_wanted motivic_smooth_product_system (k : Type) [Field k] : SmoothProductSystem k

/-- External products include every generic nilpotent length of the actual scheme product. -/
def_wanted finite_correspondence_external_product (k : Type) [Field k] (P : SmoothProductSystem k)
    (U X V Y : SmoothScheme k) (g : Generator U X) (h : Generator V Y) : ExternalGeometry P g h

def_wanted finite_correspondence_external_system (k : Type) [Field k] (P : SmoothProductSystem k) :
  ExternalSystem P

/-- The genuine product bifunctor is fixed on all cycle maps. -/
def_wanted finite_correspondence_product_functor (k : Type) [Field k]
    (D : CompositionSystem k) (G : GraphSystem k) [CorrespondenceLaws D G]
    (P : SmoothProductSystem k) (E : ExternalSystem P) : CorrespondenceProductModel D G P E

/-- The source represented presheaves retain their actual finite-correspondence actions. -/
def_wanted finite_transfer_representable_system (k : Type) [Field k]
    (D : CompositionSystem k) (G : GraphSystem k) [CorrespondenceLaws D G] [CorrespondenceAdditivity D G] :
  RepresentableSystem D G

/-- Extend the same native sheafification and its actual unit to every finite-transfer map. -/
def_wanted finite_transfer_sheafification (k : Type) [Field k]
    (D : CompositionSystem k) (G : GraphSystem k) [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)] : TransferSheafificationModel D G

def_wanted motivic_simplex_ring_maps (k : Type) [Field k] : SimplexRingMaps k
def_wanted motivic_torus_unit_ring_maps (k : Type) [Field k] : TorusRingMaps k

/-- Smooth affine, torus and simplex presentations are normalized on all actual coordinate maps. -/
def_wanted motivic_standard_schemes (k : Type) [Field k] (P : SmoothProductSystem k) : StandardSchemes P
