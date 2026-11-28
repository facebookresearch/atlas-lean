# Traub-Zenklusen: weighted tree augmentation is (1 + ln 2 + eps)-approximable

For every fixed $\varepsilon > 0$ there is a polynomial-time $(1+\ln 2+\varepsilon)$-approximation algorithm for WTAP. For small $\varepsilon$ the factor is below $1.7$; this is the first algorithm beating the factor $2$ of Frederickson and JaJa, without any bound on the ratio of link weights.

## Proof sketch

An optimal solution need not consist of non-overlapping up-links, so the algorithm does not start from it. Following Cohen and Nutov (Traub–Zenklusen, Lemma 2), replacing each link of an optimum $\mathrm{OPT}$ by the two up-link shadows towards its apex shows that an up-link solution of weight at most $2\,w(\mathrm{OPT})$ exists; shortening up-links to strict shadows makes their paths pairwise edge-disjoint without increasing the weight, and a cheapest such non-overlapping up-link solution $U_0$ is computable in polynomial time (its LP has a totally unimodular constraint matrix). Run the relative greedy algorithm from $U_0$ with $\lceil 2/\varepsilon\rceil$-thin components, and apply the decomposition theorem to $\mathrm{OPT}$ and $U_0$ with parameter $\varepsilon/2$: it gives an exceptional set $R \subseteq U_0$ with $w(R) \le \tfrac{\varepsilon}{2} w(U_0) \le \varepsilon\, w(\mathrm{OPT})$ and a partition of $\mathrm{OPT}$ into $\lceil 2/\varepsilon\rceil$-thin parts, each of which is a candidate. If $U_{i-1}$ is the current up-link set, these parts drop all of $U_{i-1} \setminus R$, so the chosen component $C_i$ satisfies $w(C_i) \le \min\{w(\mathrm{OPT})/(w(U_{i-1})-w(R)),\,1\}\cdot w(U_{i-1} \setminus U_i)$, the bound $1$ coming from singleton up-links. Summing and comparing with an integral gives $w(F) \le w(\mathrm{OPT}) + w(R) + \ln\big((w(U_0)-w(R))/w(\mathrm{OPT})\big)\,w(\mathrm{OPT}) \le (1+\ln 2+\varepsilon)\,w(\mathrm{OPT})$.

## Depends on

- [Weighted tree augmentation problem (WTAP)](weighted-tree-augmentation.md)
- [Approximation algorithms and approximation ratios](../../approximation-algorithms-and-approximation-ratios.md)

## Proof depends on

- [Relative greedy algorithms for weighted tree augmentation](relative-greedy-augmentation.md)
- [Approximate decomposition of WTAP solutions into thin components (Traub-Zenklusen)](wtap-component-decomposition.md)
- [Frederickson-JaJa: weighted tree augmentation is 2-approximable by splitting links](frederickson-jaja-two-approx.md)

## Sources

- Vera Traub, Rico Zenklusen, "A Better-Than-2 Approximation for Weighted Tree Augmentation", FOCS (2021), arXiv:2104.07114, Theorems 1, 5 and 6, Lemma 2 and Algorithm 1.
- Nachshon Cohen, Zeev Nutov, "A (1+ln 2)-Approximation Algorithm for Minimum-Cost 2-Edge-Connectivity Augmentation of Trees with Constant Radius", Theoretical Computer Science (2013).
