# Expected number of internal equilibria in random multi-player multi-strategy games

**Setting.** An infinite population plays a symmetric $d$-player game with $n$ strategies under replicator dynamics. With frequencies $x_1,\dots,x_n$ and $y_i=x_i/x_n$, the internal rest points ($0<x_i<1$) are the positive solutions $(y_1,\dots,y_{n-1})\in\mathbb R^{n-1}_{+}$ of the $n-1$ polynomial equations of degree $d-1$

$$\sum_{\substack{k_1+\dots+k_{n-1}\le d-1}}\beta^i_{k_1,\dots,k_{n-1}}\binom{d-1}{k_1,\dots,k_n}\prod_{j=1}^{n-1}y_j^{k_j}=0,\qquad i=1,\dots,n-1,$$

where $\beta^i$ are differences between the payoffs of strategy $i$ and strategy $n$ against each composition of co-players. Let the coefficient vectors $A^i=(\beta^i_{k_1,\dots,k_{n-1}})$, $i=1,\dots,n-1$, be independent centred Gaussian vectors (for the explicit two-strategy and two-player results, with independent standard normal entries), and let $E(n,d)$ be the expected number of internal equilibria.

**Theorem.**
1. $E(n,d)$ is given by the Edelman–Kostlan formula: for coefficients that are i.i.d. Gaussian vectors with covariance $C$ and monomial vector $v(y)$, the expected number of roots in $U\subseteq\mathbb R^{n-1}$ is $\pi^{-n/2}\Gamma(n/2)\int_U\big(\det[\partial_{x_i}\partial_{y_j}\log v(x)^TCv(y)]_{x=y=t}\big)^{1/2}dt$.
2. *Two strategies.* $E(2,d)=\int_0^\infty f(t)\,dt$ with an explicit density $f$, and for $d \ge 2$

$$E(2,d)\le\frac1\pi\sqrt{d-1}\sqrt{1+\frac\pi2\sqrt{d-1}};$$

hence the probability that a random $d$-player two-strategy game has the maximal number $d-1$ of internal equilibria is at most $\frac1\pi\sqrt{1+\frac\pi2\sqrt{d-1}}/\sqrt{d-1}\to0$. The expected number of stable internal equilibria is $E(2,d)/2$. (The lower bound $E(2,d)\ge\frac{d-1}{\pi\sqrt{2d-3}}$, so that $E(2,d)\to\infty$, is the case $\alpha=0$, $n=d-1$ of [Expected number of real roots of random polynomials from multiplayer games](expected-number-of-real-roots-of-random-polynomials-from-multiplayer-games.md).)
3. *Two players.* $E(n,2)=2^{1-n}$, so the probability of the maximal number of internal equilibria tends to $0$ as $n\to\infty$.

## Depends on

- [Expected number of real roots of random polynomials from multiplayer games](expected-number-of-real-roots-of-random-polynomials-from-multiplayer-games.md)

## Expansion

For two strategies the equilibrium condition is a single random polynomial in $y=x_1/x_2$ whose coefficients $\beta_k\binom{d-1}k$ are Gaussian with variances $\binom{d-1}k^2$, so the Kac–Rice (Edelman–Kostlan) density of real roots on $(0,\infty)$ is explicit, with $f(0)=\frac{d-1}\pi$ and $f(1)=\frac{d-1}{2\pi\sqrt{2d-3}}$; the bounds follow by estimating this density, giving growth between $\sqrt d$ and $d^{3/4}$ rather than the maximum $d-1$. The stable count uses the known fact that an internal equilibrium of a random two-strategy game is stable with probability $1/2$. For two-player games the system is linear, so there is at most one isolated internal equilibrium, and it exists with probability $2^{1-n}$; the paper also rederives $E(n,2)$ directly from the Edelman–Kostlan formula.

## Sources

- Manh Hong Duong and The Anh Han, "On the Expected Number of Equilibria in a Multi-player Multi-strategy Evolutionary Game", Dynamic Games and Applications 6 (2015), 324–346, <https://doi.org/10.1007/s13235-015-0148-0>; numbering as in arXiv:1408.3850: Section 2 (replicator dynamics and random polynomial theory, Edelman–Kostlan theorem) and Section 3 (results: formula for $f$, estimate for $E(2,d)$ and its corollaries, formula for $E(n,2)$).
