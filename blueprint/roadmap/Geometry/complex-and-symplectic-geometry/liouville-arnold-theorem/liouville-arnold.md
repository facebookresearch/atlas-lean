# Liouville–Arnold theorem

Let $U \subseteq \mathbb{R}^{2n}$ be open and let
$F_0, \dots, F_{n-1} \colon \mathbb{R}^{2n} \to \mathbb{R}$ be Liouville integrable on $U$. For
$c = (c_0, \dots, c_{n-1}) \in \mathbb{R}^n$, let
$M_c = \{x \in \mathbb{R}^{2n} : F_i(x) = c_i \text{ for all } i\}$ be the common level set. If
$M_c \subseteq U$ and $M_c$ is compact and connected (in particular nonempty), then $M_c$ is
homeomorphic to the $n$-torus $(\mathbb{R}/\mathbb{Z})^n$.

The hypotheses *compact* and *connected* on the level set, and its
containment in the open set where the derivatives are independent,
restore standard regularity assumptions that Knill elides; without them
the conclusion fails.

## Sources

- V. I. Arnold, *Mathematical Methods of Classical Mechanics* (2nd ed., 1989), Theorem 49.A.1 (the standard modern reference). The result is due to Liouville (1855) for the local existence of action-angle coordinates and Arnold (1963) for the compact-connected-component topology. Listed as §45 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Problem `liouville_arnold` of the lean-eval benchmark.
