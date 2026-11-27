# Semantic derivations

Let $W$ be a set of truth assignments and $\mathcal{I}$ a family of *initial sets* $I \subseteq W$. A *semantic derivation* from $\mathcal{I}$ is a sequence $S_1,\dots,S_k$ of subsets of $W$ in which every $S_t$ either is an initial set, or contains $S_i \cap S_j$ for some $i, j < t$. It is a *semantic refutation* if some $S_t = \emptyset$. Translating every line of a refutation in a sound line-based proof system with at most two premises per rule (resolution, cutting planes, Frege with binary rules) to its set of models, counting the input lines and axiom instances among the initial sets, yields a semantic refutation with the same number of lines.

## Depends on

- [Cook–Reckhow propositional proof systems](../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)
- [Line-based (dag-like) derivations](../frege-systems-and-simulations/line-based-derivations.md)

## Sources

- J. Krajíček, "Interpolation Theorems, Lower Bounds for Proof Systems, and Independence Results for Bounded Arithmetic", The Journal of Symbolic Logic 62(2), 457–486, 1997: Definition 4.1 and the remark after Definition 4.3.
