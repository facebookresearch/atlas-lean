# The GRM is the normalized cross product of the transposed matrix

For every real $N \times M$ matrix $X$ and all individuals $i, j$, the entry $A_{ij}$ of the
[genetic relationship matrix](grm.md) of $X$ equals the
[normalized cross product](../ld-score-regression/ld-corr.md) of columns $i$ and $j$ of the
transposed $M \times N$ matrix $X^\top$:

$$
A_{ij} = \frac{1}{M} \sum_{k=1}^{M} (X^\top)_{ki} (X^\top)_{kj}
= \frac{1}{M} \sum_{k=1}^{M} X_{ik} X_{jk}.
$$

The normalized cross product of two markers averages over individuals; the GRM entry of two
individuals averages over markers. Both use the convention $x/0 = 0$, so both sides are $0$ when
$M = 0$.
