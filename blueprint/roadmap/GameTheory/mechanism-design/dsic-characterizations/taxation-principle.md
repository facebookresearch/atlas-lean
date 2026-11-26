# Taxation principle

Let $M = (f, p)$ be a direct quasilinear mechanism with outcome rule $f$ and payments $p$ on valuation domains $V_i \subseteq \mathbb{R}^\Omega$. Then $M$ is dominant-strategy incentive compatible on $V$ if and only if for every agent $i$ and every report profile $b_{-i}$ of the others there are outcome prices $\pi : \Omega \to \mathbb{R}$ such that for all $v \in V_i$, agent $i$'s payment at $(v, b_{-i})$ equals $\pi(f(v, b_{-i}))$ and $f(v, b_{-i})$ maximizes $v(a) - \pi(a)$ over the range $\{f(v', b_{-i}) : v' \in V_i\}$.

## Proof sketch

Truthfulness forces two reports with the same outcome to pay the same, which defines $\pi$ on the range; incentive compatibility is then exactly the statement that the chosen outcome maximizes utility at these prices.

## Depends on

- [Incentive compatibility (quasi-linear, dominant strategies)](../vickrey-clarke-groves-mechanisms/is-incentive-compatible.md)
- [Dominant-strategy incentive compatibility](../revelation-principle/is-dominant-strategy-incentive-compatibl.md)

## Sources

- Noam Nisan, "Introduction to Mechanism Design (for Computer Scientists)", Algorithmic Game Theory, Cambridge University Press, 2007.
