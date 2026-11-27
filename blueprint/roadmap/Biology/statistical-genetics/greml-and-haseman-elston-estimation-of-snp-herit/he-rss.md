# Residual sum of squares of Haseman–Elston regression

For a real $N \times N$ matrix $A$, a vector $y \in \mathbb{R}^N$ and a slope $b \in \mathbb{R}$,
the residual sum of squares of Haseman–Elston regression is

$$\mathrm{RSS}(b) = \sum_{i<j} \bigl(y_i y_j - b\, A_{ij}\bigr)^2,$$

the sum over the [pairs](../../bioinformatics/sequence-alignment/multiple-sequence-alignment/pair-finset.md) $i < j$; it is $0$ when $N \le 1$.
