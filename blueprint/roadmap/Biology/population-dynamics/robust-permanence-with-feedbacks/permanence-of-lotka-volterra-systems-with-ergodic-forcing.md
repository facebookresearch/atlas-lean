# Permanence of Lotka–Volterra systems with ergodic forcing

Consider a Lotka–Volterra system whose intrinsic growth rates are driven by an autonomous environment,

$$\frac{dx}{dt} = x \circ \big(Ax + b(y)\big), \qquad \frac{dy}{dt} = g(y), \quad y \in K,$$

with $K \subset \mathbb{R}^m$ compact, $A = (a_{ij})$ constant and $\circ$ the componentwise product. Suppose the environmental flow on $K$ is uniquely ergodic with invariant probability $\mu$, and let $\bar b_i = \int_K b_i\,d\mu$ be the time-averaged intrinsic growth rates.

**Proposition 1.** Assume the system has a compact absorbing set (assumption S2 of the [Morse-decomposition criterion](morse-decomposition-criterion-for-robust-permanence.md)). If there are $p_1,\dots,p_n > 0$ such that

$$\sum_{i} p_i\Big(\sum_j a_{ij}x_j + \bar b_i\Big) > 0$$

for every $x \in \mathbb{R}_+^n$ with $\prod_i x_i = 0$ and $\sum_j a_{ij}x_j = -\bar b_i$ whenever $x_i > 0$ (that is, at every boundary equilibrium of the averaged system), then the forced system is robustly permanent.

**Proposition 2.** If there is no $x \in \mathbb{R}_+^n$ with $x_i > 0$ and $\sum_j a_{ij}x_j = -\bar b_i$ for all $i$ (the averaged system has no interior equilibrium), then $\omega(z) \subset S_0$ for every $z \in S \setminus S_0$: some species is driven to extinction.

Thus, when only intrinsic rates fluctuate, coexistence is decided by the autonomous Lotka–Volterra system with $b$ replaced by $\bar b$. In particular, if only the death rates of two species competing for one resource fluctuate, competitive exclusion persists; coexistence requires fluctuating interaction coefficients, such as temporally partitioned resource use.

## Depends on

- [Morse-decomposition criterion for robust permanence](morse-decomposition-criterion-for-robust-permanence.md)

## Expansion

For Proposition 2, a theorem of Hofbauer and Sigmund gives $p$ with $\sum_i p_i(\sum_j a_{ij}x_j + \bar b_i) > 0$ for all $x \in \mathbb{R}_+^n$ when no interior equilibrium exists. With $V = \sum_i p_i \ln x_i$, $\dot V = \sum_i p_i(\sum_j a_{ij}x_j + b_i(y.t))$; if some positive orbit had an $\omega$-limit point $z^*$ off $S_0$, averaging $\dot V$ along the orbit through $z^*$ and using unique ergodicity forces $V \to \infty$ there, contradicting boundedness. For Proposition 1, take the trivial Morse decomposition $\{\Gamma \cap S_0\}$ and argue by induction on the number of species present, following Hofbauer and Sigmund's proof for the autonomous case. With no species present the hypothesis gives $\sum_i p_i\bar b_i > 0$. On a face with support $J$, either the orbit converges to lower faces (handled by induction and a uniform neighborhood estimate), or the species in $J$ stay above some $\epsilon$ along times $T_m \to \infty$; then the time averages $\bar x$ of $x$ along $T_m$ satisfy $\sum_j a_{ij}\bar x_j + \bar b_i = 0$ for $i \in J$ (using $\frac{1}{T_m}\ln x_i(T_m) \to 0$ and unique ergodicity), so $\bar x$ is a boundary equilibrium of the averaged system and the hypothesis makes the weighted growth integral positive.

## Sources

- S. Patel, S. J. Schreiber, "Robust permanence for ecological equations with internal and external feedbacks", Journal of Mathematical Biology (2018), Sect. 5, Eqs. (7)–(9), Propositions 1–2 and Appendix 3, <https://doi.org/10.1007/s00285-017-1187-5>, PMCID PMC5949143.
