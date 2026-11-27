# No randomized online matching algorithm beats 1 - 1/e

For every $n \ge 1$ and every randomized online bipartite matching algorithm $\mu$ on $n$ offline vertices there is a permutation $\sigma$ such that the instance $\mathcal{T}_\sigma$ has a perfect matching of size $n$ while

$$
\mathbb{E}_\mu\big[\,|\text{matching}|\,\big] \le \Big(1 - \frac{1}{e}\Big) n + 2 .
$$

Hence the ratio $1 - 1/e$ of RANKING is optimal among randomized online algorithms against an oblivious adversary, up to an additive $O(1)$.

## Proof sketch

By Yao's principle, average over uniform $\sigma$ and bound every deterministic algorithm by the harmonic bound; choosing $s \approx n/e$ gives $n - s(H_n - H_s) \le (1 - 1/e)n + 2$.

## Depends on

- [The RANKING algorithm](ranking-algorithm.md)
- [Yao's minimax principle](../../../TheoryOfComputation/randomized-and-quantum-complexity/yao-s-minimax-principle/yao-minimax.md)

## Proof depends on

- [Harmonic upper bound for deterministic algorithms on permuted triangular instances](harmonic-bound-triangular-instances.md)
- [Yao's minimax principle](../../../TheoryOfComputation/randomized-and-quantum-complexity/yao-s-minimax-principle/yao-minimax.md)

## Sources

- R. M. Karp, U. V. Vazirani and V. V. Vazirani, "An Optimal Algorithm for On-line Bipartite Matching", Proceedings of the 22nd ACM Symposium on Theory of Computing (STOC), 1990.
