# Erdős problem 988: spherical cap discrepancy tends to infinity

For a finite set $P \subseteq S^2$, the spherical cap discrepancy is

$$D(P) = \sup_{C} \bigl\lvert\, |C \cap P| - \alpha(C)\,|P| \,\bigr\rvert,$$

where $C$ ranges over the closed spherical caps $C(v, t) = \{x \in S^2 : \langle x, v \rangle \ge t\}$ with $v \in S^2$, $t \in \mathbb{R}$, and $\alpha(C)$ is the surface measure of $C$ normalized so that $\alpha(S^2) = 1$.

Conjecture (Erdős): $\min_{|P| = n} D(P) \to \infty$ as $n \to \infty$. Precisely, for every real $M$ there is $N$ such that for every $n \ge N$ and every set $P \subseteq S^2$ of $n$ points there are $v \in S^2$ and $t \in \mathbb{R}$ with

$$\bigl\lvert\, |P \cap C(v, t)| - \alpha(C(v, t))\, n \,\bigr\rvert > M.$$

It holds; the resolution is [Erdős problem 988: cap discrepancy tends to infinity](cap-discrepancy-tends-to-infinity-holds.md).

## Sources

- T. F. Bloom, Erdős Problems, Problem #988, https://www.erdosproblems.com/988
