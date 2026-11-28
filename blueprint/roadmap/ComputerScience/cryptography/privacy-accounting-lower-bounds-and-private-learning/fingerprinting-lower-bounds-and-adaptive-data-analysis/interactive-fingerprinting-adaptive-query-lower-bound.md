# Efficient algorithms cannot answer quadratically many adaptive statistical queries

Assuming one-way functions exist, let the dimension $d$ grow with $n$ so that $2^d$ is not bounded by a polynomial in $n$. For every polynomial-time mechanism that receives $n$ samples from an unknown distribution over $\{0,1\}^d$, there is a polynomial-time analyst that, after $O(n^2)$ adaptively chosen statistical queries, causes the mechanism to give an answer with error at least a constant, with constant probability. Together with the $\tilde O(n^2)$ upper bound obtained from differential privacy, this shows that $\tilde\Theta(n^2)$ adaptive queries is the limit for efficient mechanisms. The condition on $d$ is necessary: if $n \gg 2^d$, the empirical distribution of the sample is close to the underlying distribution in statistical distance, so every statistical query can be answered accurately (Section 1 and Theorem 3.2). Unbounded computation does not remove the dependence on the data universe: over $\{\pm 1\}^d$ with $d$ sufficiently large relative to $n$, even a computationally unbounded mechanism fails after $O(n^2)$ adaptive queries, with no cryptographic assumption (Theorem 1.2 and Section 3.6, in dimension $d = O(n^2)$). Exponentially many queries in a power of $n$ can be answered only over a finite universe $\mathcal{X}$, by an inefficient mechanism whose sample size grows with $\log |\mathcal{X}|$ (Dwork et al., Theorem 1).

## Proof sketch

The analyst runs an **interactive fingerprinting code**: it adaptively issues queries whose answers on the codewords of the sample's users let it accuse users whose data influenced the answers, with each query's bias chosen from the Tardos distribution and accused users dropped from future queries. An accurate mechanism must leak, after $O(n^2)$ queries, enough to accuse every user, after which it has no information to answer correctly. Computational hardness (encrypting the data universe with a pseudorandom function) prevents the mechanism from answering by inspecting the queries themselves.

## Depends on

- [One-way functions exist](../../../../TheoryOfComputation/pseudorandomness-and-one-way-functions/impagliazzo-s-five-worlds/owfexists.md)

## Proof depends on

- [Tardos codes: optimal fully collusion-resilient fingerprinting](tardos-fingerprinting-code.md)
- [Differential privacy answers quadratically many adaptive statistical queries efficiently](adaptive-statistical-queries-via-privacy.md)

## Sources

- T. Steinke, J. Ullman, "Interactive Fingerprinting Codes and the Hardness of Preventing False Discovery", COLT (2015), arXiv:1410.1228.
- C. Dwork, V. Feldman, M. Hardt, T. Pitassi, O. Reingold, A. Roth, "Preserving Statistical Validity in Adaptive Data Analysis", STOC (2015), arXiv:1411.2664.
