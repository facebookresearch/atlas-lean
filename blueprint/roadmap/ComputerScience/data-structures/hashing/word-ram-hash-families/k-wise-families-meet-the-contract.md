# Finite k-wise independent families meet the k-wise contract

1. Every $k$-wise independent family with a finite seed set, resampled uniformly at each $\mathrm{resample}$, satisfies the exact $k$-wise contract.
2. Let a two-level family draw a top seed $\tau$ and a bottom seed $\sigma$, and suppose there is a set $G$ of top seeds with $\Pr[\tau \notin G] \le \delta$ such that for every $\tau \in G$ the family $\sigma \mapsto h_{\tau, \sigma}$ is $k$-wise independent. Then the two-level family satisfies the $\delta$-approximate $k$-wise contract.

## Proof sketch

Within one epoch, condition on the evaluated distinct keys; $k$-wise independence makes their values uniform and independent, and epochs use independent seeds. For the two-level family, couple each epoch with the ideal transcript on the event $\tau \in G$ and union-bound the failures over the epochs.

## Depends on

- [k-wise hashing contract for resamplable hash families](k-wise-hashing-contract.md)

## Sources

- J. L. Carter and M. N. Wegman, "Universal Classes of Hash Functions", Journal of Computer and System Sciences 18(2), 1979.
- M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence", Proceedings of the 54th IEEE Symposium on Foundations of Computer Science (FOCS), 2013; arXiv:1311.3121.
