# KAM theorem for twist maps (persistence of an invariant curve)

Let $\alpha$ be a
Diophantine real number and let $f : \mathbb{R} \to \mathbb{R}$ be real-analytic, $1$-periodic and
not constant, with $\int_0^1 f(x)\,dx = 0$. Then there is $c_0 > 0$ such that for every real $c$
with $|c| < c_0$ there is a $C^\infty$, strictly increasing function $q : \mathbb{R} \to \mathbb{R}$
such that $t \mapsto q(t) - t$ is $1$-periodic and, for every real $t$,

$$q(t + \alpha) - 2q(t) + q(t - \alpha) = c\, f(q(t)).$$

## Sources

- A. N. Kolmogorov (1954); V. I. Arnold (1963).
- Jürgen Moser, *On invariant curves of area-preserving mappings of an annulus*, Nachr. Akad. Wiss. Göttingen
  Math.-Phys. Kl. II (1962), 1–20.
- Oliver Knill, *Some Fundamental Theorems in Mathematics* (2023), §83 (KAM; the theorem of the section),
  <https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf>.
- Problem `kam_invariant_curve` of the lean-eval benchmark.
