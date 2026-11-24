# Pseudocount rule for nonnegative counts

Let $\iota$ be a set of parts, $c > 0$ a pseudocount and $n = (n_i)_{i \in \iota}$ real counts
with $n_i \ge 0$ for every part $i$ (zeros allowed). The pseudocount rule replaces $n$ by the
[positive composition](pos-composition.md) $n + c = (n_i + c)_{i \in \iota}$, adding the same
$c$ to every count. For a finite set of parts, the [CLR transform](clr.md) is then applied to
$n + c$.
