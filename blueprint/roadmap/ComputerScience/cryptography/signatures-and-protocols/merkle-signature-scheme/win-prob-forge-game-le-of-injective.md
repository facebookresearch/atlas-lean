# Reduction to Lamport for injective hashes

Let messages be $\ell$-bit strings with $\ell \ge 1$, and let $N \ge 1$. If $h$, as a function of
pairs, and $H$ are injective, then the probability that a forger succeeds against the $N$-key Merkle
signer is at most $N$ times the success probability of the Lamport forger built by the reduction.
Injective hash functions cannot compress: an injective $h : A \times A \to A$ needs $A$ to be
infinite or to have at most one element (stated here without proof).
