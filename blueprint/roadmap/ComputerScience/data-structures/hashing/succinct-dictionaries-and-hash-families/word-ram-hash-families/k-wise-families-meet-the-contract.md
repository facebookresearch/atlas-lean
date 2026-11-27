# Finite k-wise independent families meet the k-wise contract

1. Every $k$-wise independent family from $[U]$ to $[m]$ with a finite seed set, resampled uniformly at each $\mathrm{resample}$, satisfies the exact $k$-wise contract.
2. Let a two-level family draw at each $\mathrm{resample}$ a top seed $\tau$ and an independent bottom seed $\sigma$, each uniform on a finite set, and suppose there is a set $G$ of top seeds with $\Pr[\tau \notin G] \le \delta$ such that for every $\tau \in G$ the family $\sigma \mapsto h_{\tau, \sigma}$ is $k$-wise independent. Then the two-level family satisfies the $\delta$-approximate $k$-wise contract.

## Proof sketch

Within one epoch, condition on the evaluated distinct keys; $k$-wise independence makes their values uniform and independent, and epochs use independent seeds. For the two-level family, couple each epoch with the ideal transcript on the event $\tau \in G$ and union-bound the failures over the epochs. The sources supply $k$-wise independence (Wegman and Carter) and the two-level pattern of a top seed that is good with high probability and is then reused with fresh bottom seeds (Thorup's double tabulation, where a $k$-unique first stage is kept and only the second stage is redrawn); the contract formulation and this statement are not taken from them.

## Depends on

- [k-wise hashing contract for resamplable hash families](k-wise-hashing-contract.md)

## Sources

- M. N. Wegman and J. L. Carter, "New Hash Functions and Their Use in Authentication and Set Equality", Journal of Computer and System Sciences 22(3), 1981.
- M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence", Proceedings of the 54th IEEE Symposium on Foundations of Computer Science (FOCS), 2013; arXiv:1311.3121.
