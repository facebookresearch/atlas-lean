# Traub-Zenklusen: weighted tree augmentation is (1 + ln 2 + eps)-approximable

For every fixed $\varepsilon > 0$ there is a polynomial-time $(1+\ln 2+\varepsilon)$-approximation algorithm for WTAP. For small $\varepsilon$ the factor is below $1.7$; this is the first algorithm beating the factor $2$ of Frederickson and JaJa, without any bound on the ratio of link weights.

## Proof sketch

Run the relative greedy algorithm with components $\mathcal{K}_\varepsilon$, starting from an optimal up-link solution of weight at most $2\,\mathrm{OPT}$. By the decomposition lemma, while up-links of total weight $W$ remain there is a component of ratio at most $(1+\varepsilon)\mathrm{OPT}/W$. Integrating the resulting differential inequality from $W=\mathrm{OPT}_{\mathrm{up}}$ down to $W=\mathrm{OPT}$, and keeping the remaining up-links, of weight at most $\mathrm{OPT}$, bounds the total weight by $(1+\varepsilon)\mathrm{OPT}\ln(\mathrm{OPT}_{\mathrm{up}}/\mathrm{OPT})+\mathrm{OPT} \le (1+\ln 2+\varepsilon)\mathrm{OPT}$.

## Depends on

- [Weighted tree augmentation problem (WTAP)](weighted-tree-augmentation.md)
- [Approximation algorithms and approximation ratios](../approximation-algorithms-and-approximation-ratios.md)

## Proof depends on

- [Relative greedy algorithms for weighted tree augmentation](relative-greedy-augmentation.md)
- [Approximate decomposition of WTAP solutions into thin components (Traub-Zenklusen)](wtap-component-decomposition.md)
- [Frederickson-JaJa: weighted tree augmentation is 2-approximable by splitting links](frederickson-jaja-two-approx.md)

## Sources

- Vera Traub, Rico Zenklusen, "A Better-Than-2 Approximation for Weighted Tree Augmentation", FOCS (2021), arXiv:2104.07114.
