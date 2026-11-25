# The iteration stabilizes within the number of worlds

For an epistemic model with a finite set $W$ of worlds, a finite set $G$ of agents and $S \subseteq W$,
the stages of the [iteration for the common-knowledge region](common-knowledge-iteration.md) decrease,
$X_0 \supseteq X_1 \supseteq \cdots$, and $X_{k+1} = X_k$ for some $k \le |W|$; from then on the
stages are constant. Hence the iteration terminates after at most $|W| + 1$ steps.

## Depends on

- [Iteration for the common-knowledge region](common-knowledge-iteration.md)

## Expansion

The proof shows $X_1 \subseteq X_0$ and that $X \mapsto S \cap E_G(X)$ is monotone, so the stages
decrease; a strictly decreasing chain of subsets of $W$ has at most $|W|$ strict steps.

## Sources

- R. Rendsvig, J. Symons and Y. Wang, *Epistemic logic*, Stanford Encyclopedia of Philosophy, substantive revision
  1 December 2023, §3.2 (common knowledge by the reflexive transitive closure of the union of the
  group's relations). <https://plato.stanford.edu/entries/logic-epistemic/>
