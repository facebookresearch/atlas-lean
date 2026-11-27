# The essential supremum of a continuous map is its supremum

Let $\alpha$ be a compact topological space with its Borel $\sigma$-algebra, $\mu$ a measure on
$\alpha$ that is positive on every nonempty open set, $E$ a seminormed additive commutative group
such that $\alpha$ or $E$ is second-countable, and $f : \alpha \to E$ continuous. Then
$\|f\|_{L^\infty(\mu)} = \sup_{x \in \alpha} \|f(x)\|$, as an equality in $[0, \infty]$.

## Idea

For a continuous $f$ the sets $\{x : \|f(x)\| > t\}$ are open, and a measure positive on nonempty
open sets gives them positive measure as soon as they are nonempty, so no value of $\|f\|$ is a null
exception and the essential supremum of $\|f\|$ is its supremum. The positivity cannot be dropped:
for the zero measure every essential supremum is $0$. Compactness makes the supremum finite.

## Statements

- [The $L^\infty$ norm of a continuous map is its supremum norm](e-lp-norm-top-eq-enorm-continuous-map.md)
- [Essential supremum of a continuous map](e-lp-norm-ess-sup-eq-enorm-continuous-ma.md): the same equality for the essential supremum of $\|f\|$, used in the proof.
