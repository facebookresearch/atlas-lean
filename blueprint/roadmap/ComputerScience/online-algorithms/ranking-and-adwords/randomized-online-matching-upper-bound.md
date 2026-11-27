# No randomized online matching algorithm beats 1 - 1/e

For $n \ge 1$, let $T$ be the $n \times n$ upper-triangular $0/1$ matrix, $T_{ij} = 1$ exactly when $i \le j$. For a permutation $\sigma$ of $\{1, \dots, n\}$, the instance $\mathcal{T}_\sigma$ (Karp, Vazirani and Vazirani's $(T, \pi)$ with $\pi = \sigma$) is the online bipartite graph with $n$ offline vertices (the rows) and $n$ online vertices (the columns) whose adjacency matrix is obtained by permuting the rows of $T$ by $\sigma$, with the columns arriving in the order $n, n-1, \dots, 1$. There is a function $\delta(n) = o(n)$ such that for every $n \ge 1$ and every randomized online bipartite matching algorithm $\mu$ on $n$ offline vertices there is a permutation $\sigma$ such that the instance $\mathcal{T}_\sigma$ has a perfect matching of size $n$ while

$$
\mathbb{E}_\mu\big[\,|\text{matching}|\,\big] \le \Big(1 - \frac{1}{e}\Big) n + \delta(n) .
$$

Hence the ratio $1 - 1/e$ of RANKING is optimal among randomized online algorithms against an oblivious adversary, up to lower-order terms.

## Proof sketch

By Yao's principle (Karp, Vazirani and Vazirani, Lemma 14), it suffices to bound every deterministic algorithm on a uniformly random $\mathcal{T}_\sigma$. Making it greedy never hurts, a greedy deterministic algorithm on a uniformly random $\mathcal{T}_\sigma$ matches as many vertices in expectation as RANDOM on the unpermuted instance $\mathcal{T}_{\mathrm{id}}$ (Lemma 13), and RANDOM on $\mathcal{T}_{\mathrm{id}}$ matches $n(1 - 1/e) + o(n)$ in expectation (Lemma 16, by Kurtz's theorem); the error term depends on $n$ only.

Explicit additive constant: given the harmonic bound $n - s(H_n - H_s)$ for every $0 \le s \le n$, take $s = \lfloor n/e \rfloor$. Then $H_n - H_s = \sum_{j=s+1}^{n} 1/j \ge \ln\frac{n+1}{s+1}$ and $s + 1 \le (n + e)/e$, so $H_n - H_s \ge 1 - \ln\bigl(1 + \frac{e-1}{n+1}\bigr) \ge 1 - \frac{e-1}{n+1}$. Since $n/e - 1 \le s \le n/e$, this gives $s(H_n - H_s) \ge s - \frac{(e-1)n}{e(n+1)} \ge \frac{n}{e} - 2 + \frac1e$, hence $n - s(H_n - H_s) \le (1 - 1/e)n + 2$, so $\delta(n) = 2$ works whenever the harmonic bound holds.

## Depends on

- [The RANKING algorithm](ranking-algorithm.md)

## Proof depends on

- [Harmonic upper bound for deterministic algorithms on permuted triangular instances](harmonic-bound-triangular-instances.md)
- [Yao's minimax principle](../../../TheoryOfComputation/randomized-and-quantum-complexity/yao-s-minimax-principle/yao-minimax.md)

## Sources

- R. M. Karp, U. V. Vazirani and V. V. Vazirani, "An Optimal Algorithm for On-line Bipartite Matching", Proceedings of the 22nd ACM Symposium on Theory of Computing (STOC), 1990, Section 3 (Theorem 2, Lemmas 13, 14 and 16).
