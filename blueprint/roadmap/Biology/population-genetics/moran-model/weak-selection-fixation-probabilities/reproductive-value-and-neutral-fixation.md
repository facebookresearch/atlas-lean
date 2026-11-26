# Reproductive values and neutral fixation probability

**Setup** (shared by the pages of this folder). A population has $N$ sites, each occupied by allele $A$
(coded $1$) or $B$ (coded $0$), so states lie in $\mathbb{B}^N = \{0, 1\}^N$; write $\mathbf{A} = (1, \dots, 1)$
and $\mathbf{B} = (0, \dots, 0)$. A replacement event $(R, \alpha)$ consists of a set $R \subseteq \{1, \dots, N\}$
of replaced sites and a parentage map $\alpha : R \to \{1, \dots, N\}$; extend it to
$\tilde\alpha : \{1, \dots, N\} \to \{1, \dots, N\}$ by $\tilde\alpha(i) = \alpha(i)$ for $i \in R$ and
$\tilde\alpha(i) = i$ otherwise. In state $x$, an event is drawn with probability $p_\delta(R, \alpha \mid x)$,
and the next state is $x' = x_{\tilde\alpha}$, with $(x_{\tilde\alpha})_i = x_{\tilde\alpha(i)}$. Here
$\delta \ge 0$ is the selection intensity, and the replacement rule satisfies:

1. **Fixation Axiom.** For every $\delta$ there are a site $i$, an integer $m \ge 1$ and events
   $(R_1, \alpha_1), \dots, (R_m, \alpha_m)$ such that $p_\delta(R_k, \alpha_k \mid x) > 0$ for every $k$ and
   every $x$, $i \in R_k$ for some $k$, and $\tilde\alpha_1 \circ \dots \circ \tilde\alpha_m(j) = i$ for every
   site $j$.
2. **Neutrality.** At $\delta = 0$ the whole law of the replacement event is independent of the state:
   $p_0(R, \alpha \mid x) = p^\circ(R, \alpha)$ for all $x$.
3. **Smoothness.** For every $x$ and $(R, \alpha)$, $p_\delta(R, \alpha \mid x)$ is a smooth function of $\delta$
   in a neighbourhood of $0$.

Under the Fixation Axiom, $\mathbf{A}$ and $\mathbf{B}$ are the only absorbing states and every other state,
in $\mathbb{B}_T^N = \mathbb{B}^N \setminus \{\mathbf{A}, \mathbf{B}\}$, is transient. Let
$e_{ij}(x) = \sum_{(R, \alpha) : j \in R,\ \alpha(j) = i} p_\delta(R, \alpha \mid x)$ be the probability that
site $i$ places an offspring at site $j$ in state $x$, and $e_{ij}^\circ$ its neutral value.

**Result.** The neutral fixation probabilities $\pi_i$ of $A$ started from the state with a single $A$ at site
$i$ (the **reproductive values**) form the unique solution of

$$\sum_{j=1}^N e_{ij}^\circ \pi_j = \sum_{j=1}^N e_{ji}^\circ \pi_i \quad (1 \le i \le N), \qquad \sum_{i=1}^N \pi_i = 1.$$

Under neutral drift, for every initial state $\xi \in \mathbb{B}^N$, the reproductive-value-weighted
frequency $\hat x(t) = \sum_{i=1}^N \pi_i x_i(t)$ is a martingale started at $\hat\xi = \sum_i \pi_i \xi_i$,
and the neutral fixation probability of $A$ from $\xi$ is

$$\rho_A^\circ(\xi) = \hat\xi.$$

## Depends on

- [Martingales, submartingales and supermartingales](../../../../Probability/martingales/martingales-submartingales-and-supermartingales/martingale.md)

## Proof depends on

- [General optional stopping for uniformly integrable martingales](../../../../Probability/martingales/optional-stopping-theorem/integral-stopped-value-at-top-eq-of-unif.md)

## Expansion

1. Under neutral drift consider the ancestral-set chain $I \mapsto \tilde\alpha(I)$ on **nonempty** subsets
   of sites, driven by $p^\circ$ (the empty set is fixed by every parentage map, so it is excluded). The image of a
   singleton is a singleton, so the singletons form a closed set. By the Fixation Axiom the site $i$ of the axiom
   gives a state $\{i\}$ reachable from every nonempty set, so every closed communicating class contains
   $\{i\}$; hence there is exactly one, and it is contained in the singletons. It need not contain every
   singleton (if one site is always copied into every site, the others are never reached), so some sites can
   have reproductive value $0$. The chain therefore has a unique stationary law, supported on that class;
   $\pi_i$ is its mass at $\{i\}$. Stationarity of the singleton chain $\{i\} \mapsto \{\tilde\alpha(i)\}$ is
   the displayed linear system, and every closed class of the singleton chain is a closed class of the
   nonempty-set chain, so the singleton chain also has exactly one and the normalized solution is unique.
2. The system says $\mathbb{E}[\hat x' - \hat x \mid x] = \sum_i \pi_i \sum_j e_{ji}^\circ (x_j - x_i) = 0$,
   so $\hat x(t)$ is a martingale, with values in $[0, 1]$. It is absorbed at $\hat{\mathbf{A}} = 1$ or
   $\hat{\mathbf{B}} = 0$ almost surely. A bounded martingale is uniformly integrable, so optional stopping at the
   absorption time (which need not be bounded) gives $\rho_A^\circ(\xi) = \mathbb{E}[\hat x(\tau)] = \hat\xi$.

## Sources

- A. McAvoy and B. Allen, "Fixation probabilities in evolutionary dynamics under weak selection", Journal of Mathematical Biology 82 (2021), 14, <https://doi.org/10.1007/s00285-021-01568-4>. (Section 2.1 and Eqs. 12a–12b.)
- B. Allen and A. McAvoy, "A mathematical formalism for natural selection with arbitrary spatial and genetic structure", Journal of Mathematical Biology 78 (2019), 1147–1210, <https://doi.org/10.1007/s00285-018-1305-z>. (Theorem 7.)
