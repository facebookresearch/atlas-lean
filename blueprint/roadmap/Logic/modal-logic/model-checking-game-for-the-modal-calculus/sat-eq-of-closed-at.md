# Satisfaction depends only on the environment below the closure depth

Let $M$ be a
Kripke model, $\varphi$ a μ-calculus formula and $d$ a natural number such that $\varphi$ is
closed at depth $d$: every occurrence of a variable with de Bruijn index $n$ lying under $k$
fixpoint binders of $\varphi$ satisfies $n < d + k$. If two environments $\mathit{env}$ and
$\mathit{env}'$, each assigning a predicate on worlds to every index, agree at every index
$n < d$, then for every world $w$, $\varphi$ is satisfied at $w$ in $M$ under $\mathit{env}$ if
and only if it is satisfied at $w$ in $M$ under $\mathit{env}'$.

In particular, satisfaction of a closed formula is independent of the environment.

## Sources

- D. Kozen, *Results on the propositional μ-calculus*, Theoretical Computer Science 27 (1983), 333-354.
