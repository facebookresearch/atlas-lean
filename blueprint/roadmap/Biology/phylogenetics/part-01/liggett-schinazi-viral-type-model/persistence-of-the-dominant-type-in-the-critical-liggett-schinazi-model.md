# Persistence of the dominant type in the critical Liggett–Schinazi model

In the Liggett–Schinazi birth–death model of viral phylogenies, $N(t)$ is the number of distinct viral types alive at time $t$. New types are born at rate $\lambda N(t)$ and deaths occur at rate $N(t)$, except that a lone type cannot die. Each type receives an i.i.d. continuous fitness at birth, and at a death event the type of smallest fitness is removed; the **maximal type** is the type of largest fitness currently alive.

**Theorem.** For $\alpha \in (0,1)$,

$$\lim_{t\to\infty} \mathbb P\big(\text{the maximal types at times } \alpha t \text{ and } t \text{ coincide}\big) = \begin{cases} \alpha, & \lambda \le 1,\\ 0, & \lambda > 1. \end{cases}$$

The case $\lambda \le 1$ models influenza-like trees (one long-lived dominant lineage), $\lambda > 1$ HIV-like trees (many coexisting types).

**Critical case.** For $\lambda = 1$ let $H$ be the hitting time of state $1$ from state $2$ and $F(t) = \mathbb P(H \le t)$. Then $F$ solves the renewal equation

$$F(t) = \frac{2t}{(1+t)^3} + \int_0^t \frac{2}{(1 + t - y)^3}\,F(y)\,dy,$$

and as $h \to \infty$

$$\int_0^h t\,F'(t)\,dt \sim \log h, \qquad \int_0^h t^2 F'(t)\,dt \sim h, \qquad t\,(1 - F(t)) \to 1.$$

Consequently the time $T_n$ of the $n$-th return to a single type satisfies $T_n / (n\log n) \to 1$ in probability, which yields the theorem at $\lambda = 1$.

## Expansion

The times between visits to state $1$ are sums of a mean-one exponential holding time and an independent copy of $H$, so the dominant-type question reduces to the growth of a renewal process with heavy-tailed increments. At $\lambda = 1$ the tail $1 - F(t) \sim 1/t$ is on the boundary of finite mean, and the truncated moments above give the weak law $T_n \sim n\log n$. Laplace transforms turn the renewal equation into an algebraic one, and a Karamata Tauberian theorem converts small-$s$ asymptotics of the transform into the large-$h$ asymptotics of the truncated moments; this corrects the critical-case step of the original argument.

## Sources

- Krzysztof Bartoszek, Michał Krzemiński, "Critical case stochastic phylogenetic tree model via the Laplace transform", arXiv (2013). Theorem 1.1 (restating Liggett and Schinazi), Lemmas 2.1–2.2, Theorem 2.3 and Section 3. <https://doi.org/10.48550/arXiv.1304.7919>. Published version: Demonstratio Mathematica 47(2) (2014), 474–481, <https://doi.org/10.2478/dema-2014-0038>; locators above refer to the arXiv version.
