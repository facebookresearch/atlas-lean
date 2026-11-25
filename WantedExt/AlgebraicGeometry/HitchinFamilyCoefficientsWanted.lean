/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.HitchinFamilyCoefficients

/-!
# Characteristic sections and the normalized Hitchin family map

The first request glues actual affine characteristic polynomials of a
finite-rank line-valued endomorphism. The second supplies the actual map
from any parameter scheme to the concrete Hitchin coefficient scheme.
All coordinates are pinned to the actual characteristic sections, including
on nonreduced parameter schemes. Smooth proper curve hypotheses appear
explicitly on the private request; no properness of the Hitchin map or
NAH/P=W theorem is assumed.

Sources: Hitchin, Stable bundles and integrable systems (1987), §4;
de Cataldo--Hausel--Migliorini, https://arxiv.org/abs/1004.1420v2,
(1.3.1)--(1.3.5). Its P=W theorem is specifically rank2/degree1/twisted
character variety and is a separate endpoint, not an all-rank consequence.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.GeometricHiggsFamilies
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open MathlibExt.AlgebraicGeometry.IntegrableHiggsBundles
open MathlibExt.AlgebraicGeometry.HitchinFamilyCoefficients

universe u

/-- Glue the native local characteristic polynomial into the fixed powers. -/
def_wanted characteristicSections (X : Scheme.{u}) (L : X.Modules) (r : ℕ)
    (E : TwistedBundle X L r) : CharacteristicSections E

/-- Construct the actual normalized coefficient map on all parameter schemes.
The native proper global-section/base-change adapter remains an explicit
proof dependency; no independently supplied Hitchin projection occurs. -/
def_wanted hitchinFamilyMap (C : ComplexScheme)
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] (r : ℕ)
    (B : CoefficientChart C r) (T : ComplexScheme)
    (E : CurveFamily C T (Omega C 1) r) (K : CharacteristicSections E)
    (P : PullbackPowers (prod.fst : prod C T ⟶ C).left) : FamilyMap B E K P
