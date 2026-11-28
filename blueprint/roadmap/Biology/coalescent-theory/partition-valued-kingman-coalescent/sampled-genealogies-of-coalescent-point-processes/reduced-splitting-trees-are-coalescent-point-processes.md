# Reduced splitting trees are coalescent point processes

**Coalescent point process.** A coalescent point process (CPP) of height $T$ is a random oriented ultrametric tree of height $T$ whose node depths $H_1, \dots, H_{N-1}$ (the coalescence times between consecutive tips in the plane order) are i.i.d. copies of a random variable $H > 0$ with density $f$, stopped at the first value larger than $T$. Its **inverse tail distribution** is $F(t) = 1/\mathbb{P}(H > t)$, so $f = F'/F^2$; the number $N$ of tips is shifted geometric, $\mathbb{P}(N = n) = (1-a)a^{n-1}$ with $a = \mathbb{P}(H < T)$, and the likelihood of an oriented ultrametric tree with node depths $x_1, \dots, x_{n-1}$ is $\prod_{i=1}^{n-1} f(x_i)\,/\,F(T)$.

**Splitting trees.** Consider a binary branching process started from one particle at time $0$ in which, at time $t$, each particle gives birth to one daughter at rate $\lambda(t)$, each particle of age $x$ dies at rate $\mu(t,x)$, and the process is stopped at time $T$ conditioned on at least one particle alive (properties $(\star)$). Placing daughters to the right of mothers gives a plane-oriented tree; its **reduced tree** spans the particles alive at $T$. Let

$$g(t,s) = \mu(s, s-t)\exp\Big\{-\int_t^s \mu(u, u-t)\,du\Big\}, \qquad s \ge t,$$

be the density at time $s$ of the death time of a particle born at time $t$.

**Theorem.** The reduced tree at height $T$ of a splitting tree satisfying $(\star)$ is a CPP whose inverse tail distribution $F$ is the unique solution of

$$F'(t) = \lambda(T - t)\Big(F(t) - \int_0^t F(s)\,g(T-t, T-s)\,ds\Big), \qquad t \ge 0, \qquad F(0) = 1 .$$

For the constant-rate birth–death process ($\lambda$, $\mu$ constant and age-independent) this gives the classical $F(t) = 1 + \frac{\lambda}{\lambda - \mu}\big(e^{(\lambda - \mu)t} - 1\big)$ for $\lambda \ne \mu$.

## Depends on

- [Kendall's law of the linear birth–death process](../../../../Probability/branching-processes/linear-birth-death-process/prob.md)

## Expansion

In the plane orientation, the coalescence time between consecutive extant tips is the depth at which the contour of the tree returns below the level of the previous tip, and the independence of particle lifetimes and of the Poisson birth events along them makes these depths i.i.d. (the contour of a splitting tree is a Lévy-type process, and its excursions below successive levels decouple). The equation for $F$ follows by conditioning on the first birth event seen backward from time $T$ along the lineage of a tip: a daughter born at time $T - t$ survives to $T$ with a probability expressed through $F$, while the death density $g$ removes mothers that die before $T - s$.

## Sources

- Amaury Lambert, *The coalescent of a sample from a binary branching process*, Theor. Popul. Biol. 122 (2018), 30–35. <https://doi.org/10.1016/j.tpb.2018.04.005> Introduction (properties $(\star)$), Section "Coalescent point processes", Equation (g), Theorem 1. Locators use the numbering of the preprint, titled *The genealogy of a sample from a binary branching process*, arXiv:1710.02220.
