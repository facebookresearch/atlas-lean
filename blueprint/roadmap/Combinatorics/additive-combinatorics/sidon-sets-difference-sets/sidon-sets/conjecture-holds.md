# Large Sidon sets have many isolated sums

For every natural number $M \ge 1$ there is a
natural number $K$ such that every finite Sidon set $A$ of natural numbers with at least $K$
elements has at least $M$ isolated elements in its sumset $A + A = \{x + y : x, y \in A\}$. Here
$A$ is a Sidon set when $a + b = c + d$ with $a, b, c, d \in A$ implies $\{a, b\} = \{c, d\}$,
and an element $s$ of $A + A$ is isolated when $s + 1 \notin A + A$ and either $s = 0$ or
$s - 1 \notin A + A$.

This answers Erdős Problem 152 affirmatively: Tsoukalas et al. show, with a Lean proof, that
every Sidon set $A$ of $n$ natural numbers has at least $(n^2 - 100n - 16)/16$ isolated elements
in $A + A$.

## Sources

- George Tsoukalas et al., Advancing Mathematics Research with AI-Driven Formal Proof Search, arXiv preprint (2026), arXiv:2605.22763, https://arxiv.org/abs/2605.22763. Moved from `OpenConjectures/Combinatorics/ErdosSidonIsolatedSums`.
