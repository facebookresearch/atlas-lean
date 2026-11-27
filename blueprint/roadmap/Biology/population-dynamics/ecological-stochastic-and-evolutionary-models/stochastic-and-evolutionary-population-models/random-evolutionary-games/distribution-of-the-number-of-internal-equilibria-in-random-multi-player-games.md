# Distribution of the number of internal equilibria in random multi-player games

**Setting.** In a $d$-player two-strategy evolutionary game, a focal player using strategy $A$ (resp. $B$) facing $k$ co-players of type $A$ among the other $d - 1$ receives payoff $a_k$ (resp. $b_k$). Under the replicator dynamics for the frequency $x \in (0,1)$ of $A$, the internal equilibria correspond, via $y = x/(1-x) \in (0, \infty)$, to the positive roots of

$$P(y) = \sum_{k=0}^{d-1} \beta_k \binom{d-1}{k} y^k, \qquad \beta_k = a_k - b_k.$$

In a *random* game the payoffs are random; assume the $\beta_k$ are independent and either Gaussian, uniform, or differences of uniforms. Let $p_m$ be the probability of exactly $m$ internal equilibria, $0 \le m \le d-1$.

**Theorem.**

1. *(Exact distribution.)* $p_m = \sum_{k=0}^{\lfloor (d-1-m)/2 \rfloor} p_{m, 2k, d-1-m-2k}$, where $p_{m,2k,d-1-m-2k}$ is the probability that $P$ has $m$ positive, $2k$ non-real and $d - 1 - m - 2k$ negative roots, given by an explicit integral over root configurations of the joint density of the coefficients (Zaporozhets' formula) evaluated in closed form for each of the three coefficient laws.
2. *(Expected numbers.)* The expected numbers of internal and of stable internal equilibria are $E(d) = \sum_m m\,p_m$ and $SE(d) = \tfrac12 E(d)$.
3. *(Universal bounds, symmetric case.)* If the $\beta_k$ are i.i.d. and symmetric, then by Descartes' rule of signs

    $$p_m \le \frac{1}{2^{d-1}} \sum_{\substack{j \ge m \\ j - m \text{ even}}} \binom{d-1}{j} = \frac{1}{2^d}\Big[\sum_{j=0}^{d-1-m}\binom{d-1}{j} + \binom{d-2}{m-1}\Big].$$

    Consequently $0 \le p_m \le \tfrac12$ for all $m$, $p_{d-1} \le 2^{-(d-1)}$, $p_{d-2} \le (d-1)2^{-(d-1)}$, and $p_{d-1}, p_{d-2} \to 0$ as $d \to \infty$.

4. *(Asymmetric case.)* If $\mathbb{P}(\beta_k > 0) = \alpha$ for all $k$, the same Descartes bound holds with sign-change probabilities computed recursively in $\alpha$; in particular for $d = 2$, $p_0 = \alpha^2 + (1-\alpha)^2$ and $p_1 = 2\alpha(1-\alpha)$, and for $d = 3$, $p_1 = 2\alpha(1-\alpha)$.

## Expansion

Counting equilibria reduces to counting positive roots of a random polynomial. Zaporozhets' formula changes variables from coefficients to roots, with Jacobian the Vandermonde determinant, and integrates the coefficient density over configurations with the required numbers of positive, negative and complex roots. Descartes' rule bounds the number of positive roots by the number of sign changes $v$ with the same parity, and for i.i.d. symmetric coefficients the sign pattern is uniform on $\{\pm\}^d$, so $v$ is Binomial$(d-1, 1/2)$. Equilibria alternate in stability along $(0,1)$, which halves the expected count for stable ones. Many internal equilibria, meaning many coexisting polymorphisms, are therefore exponentially unlikely in the number of players.

## Sources

- Manh Hong Duong, Hoang Minh Tran and The Anh Han, "On the distribution of the number of internal equilibria in random evolutionary games", Journal of Mathematical Biology 78 (2019), 331–371, <https://doi.org/10.1007/s00285-018-1276-0>; numbering as in arXiv:1711.03848: Theorems 1.1–1.2, Theorem 3.1, Theorem 3.2, Corollary 3.3, Proposition 4.2, Theorem 4.5 and Theorem 4.10.
