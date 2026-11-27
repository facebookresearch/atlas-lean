# Minor-outbreak probability of the general epidemic from its branching approximation

In the general epidemic in a closed, homogeneously mixing population of $n$ individuals with $m$ initial infectives, each infective has an infectious period distributed as $I$, i.i.d. across individuals, with $0 < E(I) < \infty$, and during it makes contacts at the points of a rate-$\lambda$ Poisson process, each contact being with an individual chosen uniformly at random; a contacted susceptible becomes infective. Let $T_n$ be the total number of individuals ever infected, let $\phi$ be the Laplace transform of $I$, and let $q$ be the smallest solution in $[0, 1]$ of $q = \phi(\lambda(1 - q))$, so that $q < 1$ exactly when $R_0 = \lambda E(I) > 1$. Then for every sequence $k_n \to \infty$ with $k_n/\sqrt n \to 0$,

$$P(T_n \le k_n) \to q^m \qquad (n \to \infty),$$

that is, the probability of a minor outbreak tends to $q^m$. The proof couples the epidemic with a branching process built from the same random variables, with a birth at every contact, which agrees with the epidemic until the first contact with an already infected individual, an event of probability about $1 - e^{-k(k-1+2m)/(2n)}$ among the first $k$ contacts (Britton 2010, Section 3; Ball and Donnelly 1995). For exponential infectious periods with rate $\gamma$ (the general stochastic epidemic) the approximating process is a linear birth–death process with birth rate $\lambda$ and death rate $\gamma$, whose extinction probability from one individual is $1$ when $\lambda \le \gamma$ and $\gamma/\lambda$ when $\lambda > \gamma$, so $q = \min(1, 1/R_0)$ and the limit is $q^m = \min(1, R_0^{-m})$.

## Depends on

- [Certain extinction in the critical and subcritical cases](../../../../Probability/branching-processes/linear-birth-death-process/tendsto-extinction-prob-of-le.md)
- [Limiting extinction probability in the supercritical case](../../../../Probability/branching-processes/linear-birth-death-process/tendsto-extinction-prob-of-lt.md)

## Expansion

1. The model: the general closed epidemic, its contact processes and infectious periods, and the limiting branching process, a [Galton–Watson process](../../../../Probability/branching-processes/galton-watson-process/extinction-prob-eq-one-iff.md) in generations whose offspring law has generating function $s \mapsto \phi(\lambda(1 - s))$.
2. The coupling construction from the branching process, the role of ghost contacts, and the bound on their probability among the first $k_n$ contacts.
3. The minor-outbreak limit $q^m$; in the exponential case $q$ is the limiting extinction probability of the linear birth–death process with rates $\lambda$ and $\gamma$.
4. Separate target: the strong approximation theorem of Ball and Donnelly (1995), with strong convergence on extinction of the branching process and, on survival, strong convergence over $[0, t_N]$ under their necessary and sufficient growth conditions on $(t_N)$, stated with its exact hypotheses.

## Sources

- F. Ball and P. Donnelly, Strong approximations for epidemic models, Stochastic Process. Appl. 55 (1995), 1–21, abstract. <https://doi.org/10.1016/0304-4149(94)00034-q>
- T. Britton, Stochastic epidemic models: a survey, Math. Biosci. 225 (2010), 24–35, Section 3 (early stage approximation and example). <https://arxiv.org/abs/0910.4443>
