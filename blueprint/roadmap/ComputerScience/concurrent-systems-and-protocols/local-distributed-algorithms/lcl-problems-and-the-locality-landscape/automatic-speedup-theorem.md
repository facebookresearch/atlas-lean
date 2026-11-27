# Automatic speedup theorem for round elimination

Let $\Pi$ be a node-edge-checkable problem and let $\mathcal{G}_{n,\Delta}$ be a class of input-labelled $n$-vertex graphs of maximum degree $\Delta$ and girth at least $2t + 2$ that is $t$-independent: when a vertex that knows its radius-$(t-1)$ view extends it by one hop along one incident edge, what it sees there constrains nothing about what it may see along its other incident edges (and likewise for edges). Inputs such as vertex colourings, edge colourings and edge orientations, known at both endpoints, preserve $t$-independence, but globally unique identifiers violate it: an identifier seen along one edge cannot reappear along another. In this anonymous setting, $\Pi$ can be solved in $t \ge 1$ rounds on $\mathcal{G}_{n,\Delta}$ if and only if $\overline{\mathrm{R}}(\mathrm{R}(\Pi))$ can be solved in $t - 1$ rounds. Consequently, if $\Pi_0 = \Pi$ and $\Pi_{i+1} = \overline{\mathrm{R}}(\mathrm{R}(\Pi_i))$, the class is $t'$-independent of girth at least $2t'+2$ for all $t' \le T$, and no $\Pi_i$ with $i < T$ is $0$-round solvable, then $\Pi$ requires at least $T$ rounds. For identifiers there is a separate transfer, restricted to order-invariant algorithms: if unique identifiers are drawn from a set of at least $4\Delta^{2t}$ values, $\Pi$ has an order-invariant $t$-round algorithm exactly when $\overline{\mathrm{R}}(\mathrm{R}(\Pi))$ has an order-invariant $(t-1)$-round algorithm. Randomized versions with explicit error bounds are not part of this theorem; they are derived separately for specific problem families.

## Proof sketch

In a tree-like neighbourhood of radius $t$, the output of a node depends on its view; let each edge output the set of labels that its endpoint could output given the part of the view shared by both endpoints. High girth and $t$-independence make the possible extensions of the views of the two endpoints independent beyond the shared part, which shows the edge constraint of $\mathrm{R}(\Pi)$ is satisfied after $t - 1/2$ rounds; repeating the argument with nodes gives $\overline{\mathrm{R}}(\mathrm{R}(\Pi))$ in $t - 1$ rounds. The converse simulates one additional round to reconstruct concrete labels. For order-invariant algorithms only the relative order of identifiers matters, and with at least $4\Delta^{2t}$ identifiers available the same argument goes through.

## Depends on

- [Round elimination operators on node-edge-checkable problems](round-elimination-operators.md)
- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Sources

- S. Brandt, "An Automatic Speedup Theorem for Distributed Problems", PODC 2019, arXiv:1902.09958, Section 2.2 and Theorems 1 and 3.
