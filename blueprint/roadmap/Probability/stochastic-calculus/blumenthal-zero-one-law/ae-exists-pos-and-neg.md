# Brownian motion oscillates immediately after time zero

Let $B$ be a real Brownian motion with measurable coordinates. Then almost surely, for every $\varepsilon > 0$,
there are times $s, s' \in (0, \varepsilon]$ with $B_s > 0$ and $B_{s'} < 0$; in particular
$\sup_{0 \le s \le \varepsilon} B_s > 0$ and $\inf_{0 \le s \le \varepsilon} B_s < 0$. This is a consequence of
Blumenthal's zero–one law.

## Informally uses

- [Blumenthal zero-one law](zero-one-natural-germ.md): the event "positive at times $1/(m+1)$
  for infinitely many $m$" lies in the germ $\sigma$-algebra at time $0$, so it has probability $0$
  or $1$.
- [Half-line mass of a centered Gaussian](../../distributions/continuous/gaussian-real-ioi-zero.md): $P(B_t > 0) = 1/2$ for
  every $t > 0$, so that event has probability at least $1/2$, hence $1$.
- [Increments are independent of the past](../quadratic-variation-of-brownian-motion/indep-natural.md):
  a Brownian motion satisfies the independent-increments hypothesis of the zero-one law for its
  natural filtration.

## Sources

- J.-F. Le Gall, *Intégration, Probabilités et Processus Aléatoires*, lecture notes, École normale supérieure, Corollaire 14.4.3 (first assertion) and Théorème 14.4.2.
