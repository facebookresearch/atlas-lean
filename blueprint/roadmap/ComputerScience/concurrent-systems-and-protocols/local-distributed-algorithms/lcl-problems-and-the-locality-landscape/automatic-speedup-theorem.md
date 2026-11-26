# Automatic speedup theorem for round elimination

Let $\Pi$ be a node-edge-checkable problem on $\Delta$-regular graphs of girth greater than $2t + 2$, in the LOCAL model with or without identifiers handled through port numbering. If $\Pi$ can be solved in $t \ge 1$ rounds, then $\overline{\mathrm{R}}(\mathrm{R}(\Pi))$ can be solved in $t - 1$ rounds; conversely, if $\overline{\mathrm{R}}(\mathrm{R}(\Pi))$ can be solved in $t - 1$ rounds then $\Pi$ can be solved in $t$ rounds. In the randomized setting, a $t$-round algorithm failing with probability $p$ at each node yields a $(t-1)$-round algorithm for $\overline{\mathrm{R}}(\mathrm{R}(\Pi))$ whose local failure probability is bounded by a function of $p$, $\Delta$ and $\lvert \Sigma \rvert$ that is polynomial in $p$ for fixed $\Delta$ and $\lvert\Sigma\rvert$. Consequently, if $\Pi_0 = \Pi$ and $\Pi_{i+1} = \overline{\mathrm{R}}(\mathrm{R}(\Pi_i))$ yields a sequence where no $\Pi_i$ with $i < T$ is $0$-round solvable, then $\Pi$ requires at least $T$ rounds.

## Proof sketch

In a tree-like neighbourhood of radius $t$, the output of a node depends on its view; let each edge output the set of labels that its endpoint could output given the part of the view shared by both endpoints. High girth makes the views of the two endpoints independent beyond the shared part, which shows the edge constraint of $\mathrm{R}(\Pi)$ is satisfied after $t - 1/2$ rounds; repeating the argument with nodes gives $\overline{\mathrm{R}}(\mathrm{R}(\Pi))$ in $t - 1$ rounds. The converse simulates one additional round to reconstruct concrete labels.

## Depends on

- [Round elimination operators on node-edge-checkable problems](round-elimination-operators.md)
- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Sources

- S. Brandt, "An Automatic Speedup Theorem for Distributed Problems", PODC 2019.
