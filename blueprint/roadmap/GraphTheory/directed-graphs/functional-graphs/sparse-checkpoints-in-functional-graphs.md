# Sparse checkpoints in functional graphs

Let $f : \alpha \to \alpha$ with $\alpha$ finite and $L \ge 1$. There is a set $H \subseteq \alpha$ of at most $|\alpha|/L$ checkpoints such that every orbit either repeats a state among its first $L$ states or reaches $H$ in fewer than $2L$ steps. Refining, the checkpoints can be chosen among the active states (transient depth at least $L$, or lying on a cycle of length at least $L$), with $|H|\cdot L \le |\text{active}|$, such that every orbit repeats a state among its first $4L$ states or reaches $H$ in fewer than $4L$ steps. Closing $H$ along transient paths gives a forest whose roots and branch points can be added to $H$ at most doubling its size.

## Proof sketch

Greedily pack disjoint simple paths of $L$ states and mark the last state of each; at most $|\alpha|/L$ paths fit. An orbit whose first $L$ states are distinct cannot avoid all packed paths (else it could extend the packing), so it meets one within $L$ steps and its mark within $L - 1$ more. Restricting the packing to active states charges every checkpoint to $L$ active states; short transients are left within $2L$ steps and short cycles repeat.

## Depends on

- [Functional graphs: transient depth, cycles and canonical cycle representatives](functional-graph-transient-depth-and-cycles.md)

## Sources

- S. Schlesinger, "Square-root circuit bounds for iterated functions", 2026.
- R. Edgar, "Syncmers are more sensitive than minimizers for selecting conserved k-mers in biological sequences", PeerJ, 2021.
