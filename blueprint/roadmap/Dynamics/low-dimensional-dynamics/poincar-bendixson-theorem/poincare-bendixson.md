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

- H. Poincaré, *Mémoire sur les courbes définies par une équation différentielle*, Journal de Mathématiques 7 (1881), 8 (1882), 1 (1885), 2 (1886); I. Bendixson, *Sur les courbes définies par des équations différentielles*, Acta Mathematica 24 (1901), 1-88. Listed as §63 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). The Isabelle/HOL/AFP entry by Fabian Immler and Yong Kiam Tan (https://www.isa-afp.org/entries/Poincare_Bendixson.html) uses John Harrison's Jordan curve theorem. Problem `poincare_bendixson` of the lean-eval benchmark.
