# Discrete copula models and the flashlight transformation

**Copulas and Sklar's theorem.** A $d$-copula is a CDF $C : [0,1]^d \to [0,1]$ with uniform marginals on $[0,1]$. For every $d$-dimensional CDF $F$ with marginals $F_1, \dots, F_d$ there is a copula $C$ with

$$F(x_1, \dots, x_d) = C\big(F_1(x_1), \dots, F_d(x_d)\big) \quad \text{for all } x \in \mathbb R^d;$$

$C$ is unique if all $F_i$ are continuous and unique on $\operatorname{Ran}F_1 \times \cdots \times \operatorname{Ran}F_d$ otherwise. Conversely, any copula $C$ and univariate CDFs $F_i$ define a $d$-dimensional CDF in this way.

**Discrete marginals (spike counts).** If $X_i \in \{0, 1, 2, \dots\}$ with CDF $F_i$ (for example negative binomial), the joint probability mass function of the copula model is

$$P(X = x) = \sum_{m \in \{0,1\}^d} (-1)^{|m|}\, C\big(F_1(x_1 - m_1), \dots, F_d(x_d - m_d)\big), \qquad |m| = \textstyle\sum_i m_i,$$

a sum of $2^d$ copula evaluations (the rectangle inequality guarantees it is non-negative).

**Flashlight transformation.** Let $U \sim C$ and let $S \subseteq \{1, \dots, d\}$. Define $V_i = 1 - U_i$ for $i \in S$ and $V_i = U_i$ for $i \notin S$. Then the CDF $C_S$ of $V$ is a $d$-copula and

$$C_S(u) = \sum_{T \subseteq S} (-1)^{|T|}\, C\big(w^{T}(u)\big), \qquad w^{T}_i(u) = \begin{cases} 1 - u_i, & i \in T, \\ 1, & i \in S \setminus T, \\ u_i, & i \notin S. \end{cases}$$

$C_\emptyset = C$, and $S = \{1, \dots, d\}$ gives the survival copula. If $C$ has lower-tail dependence (as the Clayton family), $C_S$ moves it to the orthant in which coordinates in $S$ are high and the others low, leaving the dependence structure otherwise unchanged.

**Mixtures.** For copulas $C_1, \dots, C_K$ and weights $z_k \ge 0$ with $\sum_k z_k = 1$, $\sum_k z_k C_k$ is a copula; mixing flashlight-transformed Clayton copulas yields dependence concentrated in several orthants at once.

## Expansion

Sklar's theorem follows from the probability integral transform: for continuous $F_i$, $F_i(X_i)$ is uniform and its joint CDF is $C$. For discrete counts, $P(X = x)$ is the $C$-volume of the box $\prod_i (F_i(x_i - 1), F_i(x_i)]$, which expands to the alternating sum. For the flashlight transformation, $P(V \le u) = P(U_i \ge 1 - u_i,\ i \in S;\ U_j \le u_j,\ j \notin S)$; inclusion–exclusion on the complements of the events $\{U_i \le 1-u_i\}$, $i \in S$, gives the formula, and $V$ has uniform marginals because $1 - U_i$ is uniform. In prefrontal cortex recordings, negative-binomial marginals with Clayton-type copulas and flashlight-transformed mixtures fit joint spike counts better than models based on correlation alone, revealing dependence concentrated at high or at mixed count levels.

## Sources

- A. Onken, S. Grünewälder, M. H. J. Munk, K. Obermayer, "Analyzing short-term noise dependencies of spike-counts in macaque prefrontal cortex using copulas and the flashlight transformation", PLoS Computational Biology 5 (2009) e1000577, Methods (copulas and Sklar's theorem, Theorem 1; discrete marginals; flashlight transformation, Theorem 2 and Eq. 1 with proof in Text S1; mixtures of copulas), <https://doi.org/10.1371/journal.pcbi.1000577> (PMC2776173).
- R. B. Nelsen, An Introduction to Copulas, 2nd ed., Springer (2006), Chapter 2, <https://doi.org/10.1007/0-387-28678-0>.
