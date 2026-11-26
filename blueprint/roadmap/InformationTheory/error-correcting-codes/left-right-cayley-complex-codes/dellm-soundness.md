# Soundness of the vertex tester for left-right Cayley complex codes

There exist constants $\kappa_0 > 0$ and $c_0$ such that the following holds. Let $X = \mathrm{Cay}^2(A, G, B)$ with both Cayley graphs $\lambda$-spectral expanders, $|A| = |B| = \Delta$, and let $C_A \otimes C_B$ be $\kappa$-agreement testable with $C_A, C_B$ of relative distance $\delta$. If $\lambda \le c_0\, \delta^2 \kappa\, \Delta$, then the vertex tester for $C = C[G, A, B, C_A, C_B]$ satisfies

$$
\Pr[\text{reject } f] \ge \kappa_0\, \delta^{O(1)} \kappa \cdot \frac{\operatorname{dist}(f, C)}{N} \quad \text{for every } f \in \mathbb{F}_2^{X(2)}.
$$

## Proof sketch

Given $f$, replace each local view by its nearest tensor codeword; vertices whose views were already codewords are good. Agreement testability turns disagreements between adjacent local corrections along edges into a small set of bad edges; the square mixing lemma shows that bad vertices cannot percolate. An iterative local correction procedure, decreasing a potential counting conflicting edges, then reaches a codeword after changing $O(\Pr[\text{reject}] N/\kappa)$ symbols.

## Depends on

- [The local tester of a left-right Cayley complex code](lr-local-tester.md)
- [Agreement testability and robustness of tensor codes](agreement-testability-tensor.md)
- [Left-right Cayley complexes](left-right-cayley-complex.md)
- [Tensor codes on the squares of a left-right Cayley complex](square-complex-tensor-code.md)

## Proof depends on

- [Spectral expansion of the two Cayley graphs implies square-complex expansion](lr-complex-spectral.md)

## Sources

- I. Dinur, S. Evra, R. Livne, A. Lubotzky, S. Mozes, "Locally testable codes with constant rate, distance, and locality", STOC (2022), arXiv:2111.04808.
- O. Goldreich, "On the locally testable code of Dinur et al. (2021)", ECCC TR21-175 (2021).
