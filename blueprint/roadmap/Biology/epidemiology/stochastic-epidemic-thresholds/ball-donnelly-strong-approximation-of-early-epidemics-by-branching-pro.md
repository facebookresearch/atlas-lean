# Strong approximation of early epidemics by branching processes

Ball and Donnelly (1995) consider a general epidemic in a closed, homogeneously mixing population and construct, from the limiting branching process, a sequence of such epidemics indexed by the initial number of susceptibles $N$. According to the abstract of their paper, they prove strong convergence of the epidemic processes to the branching process on the event that the branching process goes extinct, and, when it does not go extinct, give necessary and sufficient conditions on a sequence $(t_N)$ for strong convergence over $[0, t_N]$, together with convergence of functionals and total variation bounds for given $N$. Britton (2010, Section 3) explains the construction: infectives have i.i.d. infectious periods with law $F_I$ and make contacts at the points of rate-$\lambda$ Poisson processes, each contact being with a uniformly chosen individual; the branching process is built from the same random variables with a birth at every contact, and it agrees with the epidemic until the first contact with an already infected individual (a ghost contact), which, among the first $k$ contacts, has probability about $1 - e^{-k(k-1+m)/2n}$. With $m$ initial infectives and $R_0 = \lambda E(I)$, the probability of a minor outbreak tends to $q^m$, where $q$ is the smallest solution of $q = \phi(\lambda(1 - q))$ and $\phi$ is the Laplace transform of $I$; for exponential infectious periods (the general stochastic epidemic) the approximating process is a linear birth–death process with birth rate $\lambda$ and death rate $\gamma$, whose extinction probability from one individual tends to $1$ when $\lambda \le \gamma$ and to $\gamma/\lambda$ when $\lambda > \gamma$, that is $q = \min(1, 1/R_0)$; with $m$ independent initial lineages the limit is $q^m = \min(1, R_0^{-m})$.

## Depends on

- [Certain extinction in the critical and subcritical cases](../../../Probability/branching-processes/linear-birth-death-process/tendsto-extinction-prob-of-le.md)
- [Limiting extinction probability in the supercritical case](../../../Probability/branching-processes/linear-birth-death-process/tendsto-extinction-prob-of-lt.md)

## Expansion

1. The model: the general closed epidemic, its contact processes and infectious periods, and the limiting branching process, a [Galton–Watson process](../../../Probability/branching-processes/galton-watson-process/extinction-prob-eq-one-iff.md) in generations.
2. The coupling construction from the branching process and the role of ghost contacts.
3. Strong convergence on extinction of the branching process.
4. Strong convergence up to $t_N$ on survival, with the necessary and sufficient growth conditions of Ball and Donnelly.
5. The minor-outbreak probability $q^m$ and the equation $q = \phi(\lambda(1-q))$; in the exponential case $q$ is the limiting extinction probability of the linear birth–death process with rates $\lambda$ and $\gamma$, which is $1$ for $\lambda \le \gamma$ and $\gamma/\lambda$ for $\lambda > \gamma$.

## Sources

- F. Ball and P. Donnelly, Strong approximations for epidemic models, Stochastic Process. Appl. 55 (1995), 1–21, abstract. <https://doi.org/10.1016/0304-4149(94)00034-q>
- T. Britton, Stochastic epidemic models: a survey, Math. Biosci. 225 (2010), 24–35, Section 3 (early stage approximation and example). <https://arxiv.org/abs/0910.4443>
