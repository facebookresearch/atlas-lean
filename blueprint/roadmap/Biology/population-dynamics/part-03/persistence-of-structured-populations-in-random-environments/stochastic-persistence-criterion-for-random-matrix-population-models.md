# Stochastic persistence criterion for random matrix population models

Let $m$ interacting species have stage-structured densities $X_t^i \in \mathbb{R}_+^{n_i}$ (row vectors) and $X_t = (X_t^1,\dots,X_t^m) \in \mathbb{R}_+^n$, evolving by

$$

X_{t+1}^i = X_t^i\,A_i(\xi_{t+1}, X_t), \qquad i = 1,\dots,m,

$$

under the hypotheses: (H1) $(\xi_t)$ is an ergodic stationary sequence in a compact Polish space; (H2) $(\xi,X) \mapsto A_i(\xi,X)$ is continuous into nonnegative $n_i \times n_i$ matrices; (H3) each $A_i$ has the fixed sign pattern of a primitive matrix; (H4) all trajectories eventually enter a compact set $S$. Let $S_0 = \{x \in S : \prod_i \|x^i\| = 0\}$ (some species absent) and $S_\eta = \{x : \min_i \|x^i\| \le \eta\}$. The long-term growth rate of species $i$ along the trajectory from $x$ is

$$

r_i(x) = \limsup_{t\to\infty} \frac1t \log\big\|A_i(\xi_1,X_0)A_i(\xi_2,X_1)\cdots A_i(\xi_t,X_{t-1})\big\|, \qquad X_0 = x .

$$

The model is **stochastically persistent** if for every $\varepsilon > 0$ there is $\eta > 0$ such that, almost surely, the empirical occupation measure $\Pi_t^x$ satisfies $\Pi_t^x(S_\eta) \le \varepsilon$ for all large $t$ and all $x \in S \setminus S_0$.

**Theorem.** Each of the following equivalent conditions implies stochastic persistence:

1. $\max_i r_i(\mu) > 0$ for every invariant probability measure $\mu$ supported on $S_0$, where $r_i(\mu)$ is the $\mu$-average of $r_i$;
2. there exist $p_1,\dots,p_m > 0$ with $\sum_i p_i\,r_i(\mu) > 0$ for every ergodic invariant measure supported on $S_0$;
3. there exist $p_1,\dots,p_m > 0$ with $\sum_i p_i\,r_i(x) > 0$ almost surely for every $x \in S_0$.

**Single species.** If $m = 1$ and the entries of $A(\xi,x)$ are non-increasing in $x$, then the population is stochastically persistent when $r_1(0) > 0$ and converges to $0$ almost surely when $r_1(0) < 0$. For the stochastic larva–pupa–adult (LPA) flour-beetle model there is a critical mean fecundity $b_{\mathrm{crit}}$ separating extinction from persistence, and $b_{\mathrm{crit}} = \mu_a/(1-\mu_l)$ when the log-survival fluctuations of all stages are identical with mean zero.

## Expansion

Because a present species is bounded, $r_i(x) \le 0$ whenever $x^i \ne 0$; so a positive growth rate can only occur at the boundary, where it measures invasion. The proof works with the skew-product random dynamical system and shows that any weak limit of empirical occupation measures that charges $S_0$ would be an invariant measure on $S_0$ on which the average $\sum_i p_i r_i$ is nonpositive, contradicting condition 2. The equivalence of the three conditions uses the ergodic decomposition and a minimax argument. In applications, autocorrelation in prey density hinders predator invasion, and the spatial storage effect allows competing species to coexist regionally.

## Sources

- Gregory Roth, Sebastian J. Schreiber, "Persistence in fluctuating environments for interacting structured populations", arXiv (2013); Journal of Mathematical Biology (2014). Section 2 (Definition 2.1), Section 3 (Theorems 3.1 and 3.4, Definitions 3.2–3.3), Section 5 (Theorems 5.1–5.2). <https://doi.org/10.48550/arXiv.1304.1862>. Published version: Journal of Mathematical Biology 69(5) (2014), 1267–1317, <https://doi.org/10.1007/s00285-013-0739-6>; locators above refer to the arXiv version.
