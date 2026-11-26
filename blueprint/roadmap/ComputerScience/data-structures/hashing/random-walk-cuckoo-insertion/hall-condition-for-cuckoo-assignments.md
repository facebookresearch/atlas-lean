# Hall's condition for valid cuckoo assignments

A valid assignment of $X$ into $Y$ exists if and only if $|N(W)| \ge |W|$ for every $W \subseteq X$, where $N(W) = \{h_i(x) : x \in W, 1 \le i \le d\}$ is the neighborhood of $W$ in the hashing graph.

## Proof sketch

This is Hall's marriage theorem applied to the bipartite hashing graph: a matching saturating $X$ exists exactly when every set of keys has at least as many neighboring slots.

## Depends on

- [d-ary cuckoo hashing and its hashing graph](d-ary-cuckoo-hashing.md)

## Proof depends on

- [d-ary cuckoo hashing and its hashing graph](d-ary-cuckoo-hashing.md)

## Sources

- Tolson Bell, Alan Frieze, "O(1) Insertion for Random Walk d-ary Cuckoo Hashing up to the Load Threshold", FOCS (2024), arXiv:2401.14394.
