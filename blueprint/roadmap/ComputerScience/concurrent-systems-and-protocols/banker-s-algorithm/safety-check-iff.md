# Correctness of the safety algorithm

For every system $S$ of claims and allocations over
a finite set $R$ of resource types, every free resource vector $w : R \to \mathbb{N}$ and every
list of pending processes, the banker's safety algorithm succeeds on $w$ and the list if and
only if the list is a safe state from $w$.
