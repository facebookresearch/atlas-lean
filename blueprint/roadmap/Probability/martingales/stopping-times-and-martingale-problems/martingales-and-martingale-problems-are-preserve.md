# Martingales and martingale problems are preserved by the usual augmentation

Let $(\Omega,\mathcal A,P)$ be a probability space, $T>0$ and $(\mathcal F_t)_{t\in[0,T]}$ a [filtration](filtrations-and-stopping-times.md). Let $\mathcal N$ be the $P$-null sets, the subsets of sets $A\in\mathcal A$ with $P(A)=0$, and let $\mathcal F^P_t=\sigma(\mathcal F_t\cup\mathcal N)$. The usual augmentation is

$$\mathcal F^{\mathrm{aug}}_t=\bigcap_{u\in(t,T]}\mathcal F^P_u\quad(t<T),\qquad\mathcal F^{\mathrm{aug}}_T=\mathcal F^P_T,$$

so no right limit is taken at the terminal time. Then:

1. Every $(\mathcal F_t)$-martingale $(M_t)_{t\in[0,T]}$ with right-continuous paths is an $(\mathcal F^{\mathrm{aug}}_t)$-martingale. Completion changes no conditional expectation, and for $s<t\le T$, $\mathbb E[M_t\mid\mathcal F^{\mathrm{aug}}_s]=\lim_n\mathbb E[M_t\mid\mathcal F^P_{s+1/n}]=\lim_nM_{s+1/n}=M_s$ by backward martingale convergence in $L^1$ and right-continuity.
2. Consequently, if a process $X$ with continuous paths solves the [martingale problem](../../markov-chains/martingale-problems/martingale-problems-generic-definition.md) for $(A,\mu)$ with respect to $(\mathcal F_t)$ on $[0,T]$, and every pair $(f,Af)$ used is bounded and continuous, then $X$ solves the same martingale problem with respect to $(\mathcal F^{\mathrm{aug}}_t)$.
3. For a continuous $(\mathcal F_t)$-adapted process with values in a metric space, hitting times of closed sets are $(\mathcal F_t)$-stopping times and hence $(\mathcal F^{\mathrm{aug}}_t)$-stopping times, and hitting times of open sets are $(\mathcal F^{\mathrm{aug}}_t)$-stopping times, by [usual conditions and continuous-time hitting times](../../markov-chains/finite-continuous-time-markov-chains/hitting-times-of-finite-continuous-time-markov-c/usual-conditions-and-continuous-time-hitting-tim.md), since $(\mathcal F^{\mathrm{aug}}_t)$ is complete and right-continuous.

## Depends on

- [Filtrations and stopping times](filtrations-and-stopping-times.md)
- [Martingale problems (generic definition)](../../markov-chains/martingale-problems/martingale-problems-generic-definition.md)
- [Usual conditions and continuous-time hitting times](../../markov-chains/finite-continuous-time-markov-chains/hitting-times-of-finite-continuous-time-markov-c/usual-conditions-and-continuous-time-hitting-tim.md)

## Proof depends on

- [General optional stopping for uniformly integrable martingales](../optional-stopping-theorem/integral-stopped-value-at-top-eq-of-unif.md)

## Expansion

A full proof establishes that $\mathbb E[Y\mid\sigma(\mathcal G\cup\mathcal N)]=\mathbb E[Y\mid\mathcal G]$ almost surely, the backward (Lévy downward) martingale convergence theorem, right-continuity of $(\mathcal F^{\mathrm{aug}}_t)$ for $t<T$, and the hitting-time statements. It should also check:

- without right-continuity of $M$ the identity $\mathbb E[M_t\mid\mathcal F_{s+}]=M_s$ can fail;
- a non-dyadic horizon such as $T=1/3$, where $\mathcal F^{\mathrm{aug}}_T=\mathcal F^P_T$ and right limits are taken only at $t<1/3$;
- for a filtration that jumps exactly at $T$, $\mathcal F^{\mathrm{aug}}_T$ is the completed $\mathcal F_T$, with no intersection over $u>T$.

## Sources

- D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Grundlehren 293, Springer, 1999, <https://link.springer.com/book/10.1007/978-3-662-06400-9>, augmentation and martingales (topic).
- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in Mathematics 113, Springer, 1991, <https://link.springer.com/book/10.1007/978-1-4612-0949-2>, usual augmentation of filtrations (Ch. 1, topic).
