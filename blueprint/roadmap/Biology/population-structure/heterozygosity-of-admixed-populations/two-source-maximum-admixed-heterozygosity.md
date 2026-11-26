# Maximum admixed heterozygosity for two source populations

Take $K = 2$ sources with distinct allele-frequency vectors $p_1 \ne p_2$, heterozygosities $H_1, H_2$, between-source mismatch probability $C_{12}$, $H_S = (H_1 + H_2)/2$, pooled heterozygosity $H_T = (H_1 + H_2 + 2C_{12})/4$ and pairwise $F_{12}$. With $\gamma_2 = 1 - \gamma_1$, [the admixed heterozygosity](admixed-heterozygosity-decomposition-and-lower-bound.md) is the concave quadratic

$$H_{\mathrm{adm}}(\gamma_1) = \gamma_1^2 H_1 + 2\gamma_1(1-\gamma_1)C_{12} + (1-\gamma_1)^2 H_2, \qquad \gamma_1 \in [0,1].$$

**Proposition 7.** The maximizer $\gamma_1^*$ is as follows.

1. If $H_1 < C_{12}$ and $H_2 < C_{12}$, then $\gamma_1^* \in (0,1)$ with

$$\gamma_1^* = \frac{C_{12} - H_2}{2(C_{12} - H_S)} = \frac12 + \frac{H_1 - H_2}{8(H_T - H_S)}, \qquad H_{\mathrm{adm}}(\gamma_1^*) = \frac{C_{12}^2 - H_1H_2}{2(C_{12} - H_S)} = H_T + \frac{(H_1 - H_2)^2}{16(H_T - H_S)}.$$

2. If $H_1 < C_{12} \le H_2$, then $\gamma_1^* = 0$ and the maximum is $H_2$.
3. If $H_2 < C_{12} \le H_1$, then $\gamma_1^* = 1$ and the maximum is $H_1$.

**Corollaries 8–10.** $\gamma_1^* \ge 1/2$ if and only if $H_1 \ge H_2$. The maximum is at least $H_T$, with equality when $H_1 = H_2$. The maximizer is interior if and only if

$$F_{12} > \frac{|H_1 - H_2|}{2(H_1 + H_2) + |H_1 - H_2|}.$$

The right-hand side is at most $1/3$, so $F_{12} > 1/3$ always gives an interior optimum.

**Proposition 11 (biallelic locus).** With $J = 2$ and frequencies $p_{11} \ne p_{21}$ of the first allele, the maximizer is interior exactly when $1/2$ lies strictly between $p_{11}$ and $p_{21}$. Then

$$\gamma_1^* = \frac{1 - 2p_{21}}{2(p_{11} - p_{21})}, \qquad H_{\mathrm{adm}}(\gamma_1^*) = \frac12 .$$

Otherwise the optimum is the vertex of the source whose frequency is closer to $1/2$.

**Proposition 17.** If $p_{11}, p_{21}$ and $\gamma_1$ are independent and uniform on $[0,1]$ ($J = 2$), then $\Pr[H_{\mathrm{adm}}(\gamma_1) > \max\{H_1, H_2\}] = 1 - \log 2 \approx 0.307$.

## Depends on

- [Heterozygosity of an admixed population and its lower bound](admixed-heterozygosity-decomposition-and-lower-bound.md)
- [Maximum heterozygosity of an admixed population over the admixture simplex](maximum-admixed-heterozygosity-over-the-simplex.md)

## Expansion

The leading coefficient is $H_1 + H_2 - 2C_{12} = -4(H_T - H_S) < 0$ because $p_1 \ne p_2$, so there is one critical point. Setting the derivative to zero gives case 1; when the critical point leaves $[0,1]$ the maximum sits at the nearer endpoint (cases 2 and 3). Both $H_1 \ge C_{12}$ and $H_2 \ge C_{12}$ cannot hold at once, since $C_{12} - H_S = 2(H_T - H_S) > 0$. Corollary 10 rewrites $0 < \gamma_1^* < 1$ using $C_{12} = H_S(1 + F_{12})/(1 - F_{12})$. For $J = 2$ one finds $C_{12} - H_2 = (p_{11} - p_{21})(1 - 2p_{21})$ and $C_{12}^2 - H_1H_2 = C_{12} - H_S = (p_{11} - p_{21})^2$, giving Proposition 11. Proposition 17 integrates over the two off-diagonal quadrants of the unit square where $1/2$ separates the frequencies, together with the length of the $\gamma_1$ interval on which the quadratic exceeds both endpoint values.

## Sources

- S. M. Boca, L. Huang and N. A. Rosenberg, "On the heterozygosity of an admixed population", *Journal of Mathematical Biology* 81 (2020), 1217–1250, <https://doi.org/10.1007/s00285-020-01531-9> (PMC7710588), Section 4 (Proposition 7, Corollaries 8–10, Proposition 11), Appendix 2 (proofs) and Appendix 3 (Proposition 17).
