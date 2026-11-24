# Iteration for the common-knowledge region

Let $M$ be an epistemic model whose set $W$ of worlds is finite, with decidable accessibility
relations $R_i$, let $G$ be a finite set of agents, and let $S \subseteq W$. For $X \subseteq W$ put
$E_G(X) = \{w \in W : v \in X \text{ for every } i \in G \text{ and every } v \text{ with }
w \mathrel{R_i} v\}$, the worlds at which every member of $G$ considers only worlds of $X$ possible.
The iteration for the common-knowledge region of $S$ is the sequence

$$X_0 = S, \qquad X_{k+1} = S \cap E_G(X_k),$$

and its output is $X_k$ for the least $k$ with $X_{k+1} = X_k$. Each step is computable: $W$ and $G$
are finite and membership in $X_k$ and in each $R_i$ is decidable. When $G$ is empty, $E_G(X) = W$
for every $X$, so the output is $S$ itself.

## Depends on

- [Epistemic models](../model.md)

## Expansion

The page fixes the computation as a function of the finite model, the finite group and a decidable
set $S$; the input $S$ is, in use, the set of worlds satisfying a formula, computed by recursion on
the formula. Formulas containing public announcements are outside this node.

## Sources

- R. Rendsvig, J. Symons and Y. Wang, *Epistemic logic*, Stanford Encyclopedia of Philosophy, substantive revision
  1 December 2023, §3.2 (common knowledge by the reflexive transitive closure of the union of the
  group's relations). <https://plato.stanford.edu/entries/logic-epistemic/>
