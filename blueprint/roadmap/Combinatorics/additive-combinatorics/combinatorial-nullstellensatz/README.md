# Combinatorial Nullstellensatz

If a polynomial $f$ over a field has degree $\sum_i t_i$ and the coefficient of
$\prod_i x_i^{t_i}$ is nonzero, then $f$ does not vanish on any grid $S_1 \times \dots \times S_n$
with $|S_i| > t_i$. Alon derives this from a structural statement: a polynomial vanishing on the
grid is a combination $\sum_i h_i g_i$ of the polynomials $g_i = \prod_{s \in S_i}(x_i - s)$ with
controlled degrees. Choosing $f$ to encode a combinatorial configuration gives short proofs of the
Chevalley–Warning theorem, the Cauchy–Davenport theorem, the Erdős–Heilbronn conjecture on sums of
distinct elements, the Erdős–Ginzburg–Ziv theorem (through the permanent lemma), results on regular
subgraphs and on covering the cube by hyperplanes, and the Alon–Tarsi theorem on list colourings.
The presentation follows Noga Alon, "Combinatorial Nullstellensatz", *Combin. Probab. Comput.* 8
(1999) 7–29.

The pages below state both forms of the Nullstellensatz in the paper's notation, the paper's
existence form of the Chevalley–Warning theorem, the Erdős–Heilbronn bound for the restricted
sumset $2^{\wedge}A$ in $\mathbb{Z}_p$ (with its reformulation as the case $h = 2$ of the
Dias da Silva–Hamidoune theorem), and the Alon–Füredi theorem on covering the cube minus one vertex
by hyperplanes. Further consequences in the paper include the Cauchy–Davenport theorem for
$\mathbb{Z}_p$ (Theorem 3.2) and the Erdős–Ginzburg–Ziv theorem for primes (Proposition 8.2).

- [Combinatorial Nullstellensatz, Theorem 1.1](exists-eq-sum-mul-of-vanishing.md)
- [Combinatorial Nullstellensatz, Theorem 1.2](exists-eval-ne-zero.md)
- [Chevalley–Warning theorem, existence form](exists-ne-common-zero.md)
- [Erdős–Heilbronn conjecture (Dias da Silva–Hamidoune theorem)](min-le-card-restricted-sumset.md)
- [Dias da Silva–Hamidoune theorem for h = 2](dias-da-silva-hamidoune-two.md)
- [Covering the cube minus a vertex by hyperplanes (Alon–Füredi)](le-card-of-covers.md)

## Related topics

- [Sumsets and inverse theorems](../sumsets-inverse-theorems/README.md): the Cauchy–Davenport–Chowla and Vosper theorems on sumsets modulo $q$, of which the restricted-sum bound is a variant.
- [Zero-sum problems and subset sums](../zero-sum-subset-sums/README.md): zero-sum results of Erdős–Ginzburg–Ziv type, which the paper reaches through the permanent lemma.
- [Sumsets with at least r distinct terms](../sumsets-inverse-theorems/sumsets-with-at-least-r-distinct-terms/README.md): the general Dias da Silva–Hamidoune theorem for sums of $h$ distinct elements, whose case $h = 2$ is the Erdős–Heilbronn bound.
