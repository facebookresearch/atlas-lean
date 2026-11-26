# Law of the hitting time of a level

Let $B$ be a real Brownian motion with continuous paths and $a > 0$. For every $t \ge 0$,

$$P\bigl(B_s = a \text{ for some } s \in [0, t]\bigr) = \int_0^t \frac{a}{\sqrt{2\pi s^3}} \exp\Bigl(-\frac{a^2}{2s}\Bigr) ds .$$

Since $T_a = \inf\{t \ge 0 : B_t = a\} \le t$ exactly when the path reaches $a$ on $[0, t]$, the hitting
time $T_a$ has density $a (2\pi s^3)^{-1/2} e^{-a^2/(2s)}$ on $(0, \infty)$.

## Informally uses

- [The running maximum has the law of $|B_t|$](map-i-sup-eq-map-abs.md):
  $P(T_a \le t) = P(S_t \ge a) = P(|B_t| \ge a) = P(t B_1^2 \ge a^2)$ by scaling, and differentiating in
  $t$ gives the density.

## Sources

- J.-F. Le Gall, *Intégration, Probabilités et Processus Aléatoires*, lecture notes, École normale supérieure, Corollaire 14.5.3.
