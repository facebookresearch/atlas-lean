# Least fixed point equals one iff mean offspring is at most one

Let $\nu$ be a probability measure on $\mathbb{N}$ with $\nu(\{1\}) \ne 1$, let
$f(s) = \sum_{k \ge 0} \nu(\{k\})\, s^k$ be its generating function and let $m \in [0, \infty]$ be
its [mean](mean.md). Then $\sup_{n \in \mathbb{N}} f^{\circ n}(0) = 1$ if and only if $m \le 1$.
By [the least fixed point property](is-least-i-sup-iterate-pgf-zero.md), the supremum is the
least fixed point of $f$ in $[0, 1]$.

## Sources

- K. B. Athreya and P. E. Ney, *Branching Processes*, Springer, 1972, Chapter I.
