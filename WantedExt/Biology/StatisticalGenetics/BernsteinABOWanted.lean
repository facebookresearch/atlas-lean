/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bernstein's triple-allele law for the ABO blood groups

Bernstein (1924, 1925) explained the ABO blood groups by one locus with three alleles `O`, `A`,
`B` at frequencies `r`, `p`, `q` (`p + q + r = 1`). Under Hardy–Weinberg proportions the
phenotype frequencies are `O = r²`, `A = p² + 2pr`, `B = q² + 2qr` and `AB = 2pq` (Crow 1993,
Table 1), so `r = √O`, `p = 1 - √(O + B)` and `q = 1 - √(O + A)`, and these three estimates sum
to `1` exactly under the model. The rival model of von Dungern and Hirszfeld puts the `A` and `B`
antigens at two independent loci; with Hardy–Weinberg and linkage equilibrium it forces
`(A + AB)(B + AB) = AB`, the relation Bernstein used to reject it (Crow 1993, p. 4).

The square-root identities of the triple-allele model (derived from Crow's Table 1; they are not
printed in that table) are proved in
`Domains.Biology.StatisticalGenetics.BernsteinABOSqrtEstimates`.
Recorded here: the fact (derived) that the triple-allele model never satisfies the two-locus
constraint when both `A` and `B` alleles are present, so the two models are distinguishable
from phenotype frequencies alone. The two-locus constraint is proved in
`Domains.Biology.StatisticalGenetics.BernsteinABOTwoLocusConstraint`. Hardy–Weinberg
proportions are inputs. The numerical rejection on Bernstein's data and any likelihood
comparison are not formalized.

Sources: F. Bernstein, Klin. Wochenschr. 3 (1924) 1495–1497; F. Bernstein, Z. indukt.
Abstamm.- Vererbungsl. 37 (1925) 237–270; J. F. Crow, "Felix Bernstein and the first human
marker locus", Genetics 133 (1993) 4–7, p. 4 and Table 1.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import Domains.Biology.StatisticalGenetics.BernsteinABOSqrtEstimates
public import Domains.Biology.StatisticalGenetics.BernsteinABOTwoLocusConstraint

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.BernsteinABOWanted

end WantedExt.Biology.StatisticalGenetics.BernsteinABOWanted
