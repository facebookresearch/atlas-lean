/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.IntegralTiltModels

/-!
# Canonical all-rank perfectoid tilt point comparison

Scholze, *Etale cohomology of diamonds*, arXiv:1709.07343v4,
Theorem 3.12, p17: |f(x-flat)| = |f-sharp(x)| defines the homeomorphism
of the two actual Spa point spectra and transports rational domains.

The integral inverse limit, sharp map, actual localization and topology,
plus ring and denominator are already fixed. Completed Tau local tilt
and generic adic gluing are source integration inputs, not new raw
constructor requests. No ringed-space isomorphism across characteristics
is asserted. General finite-etale/site and model-globalization companions
remain separate canonical comparisons.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CanonicalTiltPoints

open MathlibExt.RingTheory.CompleteHuberPairModels
open MathlibExt.AlgebraicGeometry.IntegralTiltModels

/-- **The tilting homeomorphism of adic spectra.** Scholze, *Étale cohomology of diamonds*, Theorem
3.12: for a prime $p$, a perfectoid pair $P$ with the integral input `D` ($P^\circ$ is $p$-adically
complete, $p$ is not a unit in it, and a compatible system of $p$-power roots of a
pseudo-uniformizer in $P^\circ$) and a tilt model `M` (a characteristic-$p$ perfectoid pair
identified with the tilt of $P$), a homeomorphism from $\operatorname{Spa} P$ to the adic spectrum
of `M` under which, for all $a, b$ in the inverse limit $\varprojlim_{x \mapsto x^p} P^\circ / p$,
$|a| \le |b|$ at the image of a point $v$ exactly when $|a^\sharp| \le |b^\sharp|$ at $v$. -/
public def_wanted tiltingPoints
    (p : ℕ) [Fact p.Prime] (P : PerfectoidPair p)
    [D : IntegralInput p P] (M : TiltModel p P (D := D)) :
    TiltingPoints p P M

end WantedExt.AlgebraicGeometry.CanonicalTiltPoints
