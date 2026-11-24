# The running maximum has the law of $|B_t|$

Let $B$ be a real Brownian motion with measurable coordinates and continuous paths, and $t > 0$. Then
$S_t = \sup_{0 \le s \le t} B_s$ has the same law as $|B_t|$.

## Informally uses

- [Reflection principle](reflection-principle.md): with $b = a$,
  $P(S_t \ge a) = P(S_t \ge a, B_t \le a) + P(B_t > a) = 2 P(B_t \ge a) = P(|B_t| \ge a)$.

## Sources

- J.-F. Le Gall, *Intégration, Probabilités et Processus Aléatoires*, lecture notes, École normale supérieure, Théorème 14.5.2, second assertion.
