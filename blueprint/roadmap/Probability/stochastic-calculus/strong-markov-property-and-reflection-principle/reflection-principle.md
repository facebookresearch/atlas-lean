# Reflection principle

Let $B$ be a real Brownian motion with continuous paths, $S_t = \sup_{0 \le s \le t} B_s$, $t > 0$, $a \ge 0$
and $b \le a$. Then

$$P(S_t \ge a,\ B_t \le b) = P(B_t \ge 2a - b) .$$

It is proved by applying the strong Markov property at the hitting time of $a$.

## Informally uses

- [Strong Markov property of Brownian motion](strong-markov.md): applied at the hitting time
  $T_a$, where $B_{T_a} = a$; the restarted motion is replaced by its reflection $-B^{(T_a)}$,
  which has the same law and is also independent of $T_a$.
- [Linear Brownian motion hits every level](../construction-and-sample-paths-of-brownian-motion/ae-exists-eq.md):
  the proof uses $T_a < \infty$ almost surely (Corollaire 14.4.3 of the ENS notes).

## Sources

- J.-F. Le Gall, *Intégration, Probabilités et Processus Aléatoires*, lecture notes, École normale supérieure, Théorème 14.5.2.
