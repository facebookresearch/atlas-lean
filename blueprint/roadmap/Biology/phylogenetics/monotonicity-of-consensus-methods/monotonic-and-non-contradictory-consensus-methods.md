# Monotonic and non-contradictory consensus methods

**Definitions.** A consensus method $\phi$ maps a profile $\mathcal P=(T_1,\dots,T_k)$ of phylogenetic $X$-trees to a single $X$-tree. Write $T\preceq T'$ ($T'$ refines $T$) if every cluster (rooted case) or split (unrooted case) of $T$ is a cluster/split of $T'$.

- $\phi$ is **monotonic** if $T_i\preceq T_i'$ for all $i$ implies $\phi(\mathcal P)\preceq\phi(\mathcal P')$: resolving previously unresolved clades in the input can only refine the consensus, never contradict it.
- $\phi$ is **non-contradictory** if every cluster (split) of $\phi(\mathcal P)$ is compatible with at least one input tree, and **co-Pareto** if every cluster (split) of $\phi(\mathcal P)$ is displayed by at least one input tree.

**Theorem.**

1. Strict consensus and majority-rule consensus $\mathtt{MR}_p$ ($p>50$) are monotonic and non-contradictory.
2. Loose (semi-strict), Adams and Aho consensus are not monotonic; they become monotone on refined profiles that are linearly ordered by $\preceq$. Adams and Aho consensus are not non-contradictory.
3. The supertree methods MRP (matrix representation with parsimony) and MRC (matrix representation with compatibility) are not monotonic; MRP is not non-contradictory, while MRC is co-Pareto.
4. If $\phi$ is monotonic and unanimous, then $\mathtt{strict}(\mathcal P)\preceq\phi(\mathcal P)$ for every profile; if moreover every cluster of every input tree is compatible with all input trees, then $\phi(\mathcal P)\preceq\mathtt{loose}(\mathcal P)$.
5. If $\phi$ is regular and monotonic, every cluster (split) of $\phi(\mathcal P)$ is compatible with every cluster (split) of $\mathtt{loose}(\mathcal P)$, and $\phi(\mathcal P)$ contains neither of two clusters that are compatible with all input trees but not with each other.
6. Every monotonic, non-contradictory consensus method is co-Pareto.

Infinitely many consensus methods are regular, monotonic and non-contradictory.

## Expansion

The key lemma is that any cluster $c\notin\mathcal C(T)$ that is compatible with $T$ can be contradicted by some refinement $T'$ of $T$. If a monotonic method output a cluster absent from all input trees, refining the inputs to contradict it would force the output to keep a cluster incompatible with every refined input, violating non-contradiction; this proves item 6, and similar refinement arguments give items 4 and 5. Counterexamples on four or five taxa show that Adams, Aho, loose consensus and the matrix-representation methods can produce a consensus tree that a later refinement of the inputs contradicts.

## Sources

- Mareike Fischer, Michael Hendriksen, "A survey of the monotonicity and non-contradiction of consensus methods and supertree methods", arXiv:2102.04502 (2021), Theorem 3.1 (from earlier work of McMorris and coauthors), Propositions 3.2–3.4 and 3.6, Theorems 3.5 and 3.7–3.10, Corollaries 3.13–3.15, Theorem 3.16 and Lemma 3.17, <https://doi.org/10.48550/arXiv.2102.04502>.
