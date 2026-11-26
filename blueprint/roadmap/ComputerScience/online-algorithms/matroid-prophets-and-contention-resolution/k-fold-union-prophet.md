# Prophet inequalities approaching 1 for k-fold matroid unions

For every matroid $\mathcal{M}$ and every $k \ge 2$, the $k$-fold union $\mathcal{M}^{(k)}$ admits a prophet inequality with competitive ratio $1 - O\!\left(\sqrt{\frac{\log k}{k}}\right)$, obtained from an online contention resolution scheme with the same selectability.

## Proof sketch

The OCRS selects an active element if it can be added while every element of the $k$-fold union stays coverable with slack; the key ingredient is a bicriterion concentration inequality for monotone $1$-Lipschitz functions of independent items, applied to the rank of the active set restricted to the remaining elements, which yields Chernoff-strength concentration even though the rank function is not self-bounding. Concentration at scale $\sqrt{k \log k}$ relative to capacity $k$ gives the loss $O(\sqrt{\log k / k})$.

## Depends on

- [k-fold matroid unions](k-fold-matroid-union.md)
- [An OCRS yields a prophet inequality](ocrs-implies-prophet-inequality.md)
- [Prophet inequality for k-uniform matroids](k-uniform-prophet.md)

## Proof depends on

- [k-fold matroid unions](k-fold-matroid-union.md)
- [An OCRS yields a prophet inequality](ocrs-implies-prophet-inequality.md)
- [Prophet inequality for k-uniform matroids](k-uniform-prophet.md)

## Sources

- Noga Alon, Nick Gravin, Tristan Pollner, Aviad Rubinstein, Hongao Wang, S. Matthew Weinberg, Qianfan Zhang, "A Bicriterion Concentration Inequality and Prophet Inequalities for k-Fold Matroid Unions", ITCS (2025).
