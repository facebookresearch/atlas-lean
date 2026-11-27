# Strong Markov property of Brownian motion

Let $B$ be a real Brownian motion with measurable coordinates and continuous paths, and $T$ a stopping
time of its natural filtration, with values in $[0, \infty]$ and $P(T < \infty) > 0$. Then under the
conditional probability $P(\cdot \mid T < \infty)$, the process $B^{(T)}_t = B_{T + t} - B_T$, $t \ge 0$, is a
Brownian motion and is independent of the $\sigma$-algebra $\mathcal F_T$ of events prior to $T$.

## Informally uses

- [Conditional expectation of a future path functional](../markov-property-of-processes-with-independent-in/independent-increments-cond-exp.md):
  the simple Markov property at deterministic times, applied at the dyadic approximations
  $T_n = \lceil 2^n T \rceil / 2^n$ of $T$, which decrease to $T$; path continuity passes to the limit.

## Sources

- J.-F. Le Gall, *Intégration, Probabilités et Processus Aléatoires*, lecture notes, École normale supérieure, Théorème 14.5.1.
- J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Graduate Texts in Mathematics 274, Springer, 2016, Chapter 2, section "The strong Markov property of Brownian motion".
