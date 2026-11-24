# Poincaré–Bendixson theorem

Let $F \colon \mathbb{R}^2 \to \mathbb{R}^2$ be a continuously
differentiable vector field on the Euclidean plane, and let
$\gamma \colon \mathbb{R} \to \mathbb{R}^2$ be a curve such that for every $t \ge 0$ the derivative
of $\gamma$ at $t$ within $[0, \infty)$ is $F(\gamma(t))$. Let
$\omega(\gamma) = \bigcap_{s \in \mathbb{R}} \overline{\gamma([s, \infty))}$ be the $\omega$-limit
set of $\gamma$. Then at least one of the following holds: the forward orbit
$\gamma([0, \infty))$ is unbounded; $\omega(\gamma)$ contains a point $x_0$ with $F(x_0) = 0$; or
there are a real number $T > 0$ and a curve $\beta \colon \mathbb{R} \to \mathbb{R}^2$ with
$\beta'(t) = F(\beta(t))$ and $\beta(t + T) = \beta(t)$ for every real $t$ and with
$F(\beta(0)) \ne 0$, such that $\omega(\gamma)$ equals the range of $\beta$.

## Sources

- Henri Poincaré, *Mémoire sur les courbes définies par une équation différentielle*, J. Math. Pures Appl. (3) 7
  (1881), 8 (1882); (4) 1 (1885), 2 (1886).
- Ivar Bendixson, *Sur les courbes définies par des équations différentielles*, Acta Math. 24 (1901), 1–88,
  DOI 10.1007/bf02403068.
- Oliver Knill, *Some Fundamental Theorems in Mathematics* (2023), §63 (Differential equations), <https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf>.
- Fabian Immler and Yong Kiam Tan, *The Poincaré–Bendixson theorem*, Archive of Formal Proofs,
  <https://www.isa-afp.org/entries/Poincare_Bendixson.html> (a proof through John Harrison's Jordan curve theorem).
- Problem `poincare_bendixson` of the lean-eval benchmark.
