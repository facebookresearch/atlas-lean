# Fair-bit block rejection sampling: exact law, capped trials and expected cost

Fix a block width $w \ge 1$ and a decoder $D : \{0,1\}^w \to \alpha \cup \{\mathrm{reject}\}$. Let $a = \Pr[D(U) \ne \mathrm{reject}]$ for a uniform block $U$, and when $a > 0$ let $\pi(x) = \Pr[D(U) = x]/a$. The *block rejection sampler* reads independent uniform blocks and outputs $D$ of the first block that is not rejected.

1. Capped at $t$ blocks, it fails with probability exactly $(1-a)^t$, and any completion that outputs a fixed fallback value on failure has total variation distance at most $(1-a)^t$ from $\pi$.
2. Without a cap it is a DDG tree that, after $n$ fair bits, has the law of the sampler capped at $\lfloor n/w \rfloor$ blocks; if $a > 0$ it generates $\pi$ with expected number of fair bits exactly $w/a$.
3. (Uniform integers) For $n \ge 1$, decoding $\lceil \log_2 n \rceil$ bits as a binary integer and rejecting values $\ge n$ generates the uniform distribution on $\{0, \dots, n-1\}$ with at most $2\lceil \log_2 n\rceil$ expected fair bits (exactly $k$ when $n = 2^k$), and its $t$-block cap fails with probability at most $2^{-t}$.

## Proof sketch

Blocks are independent, so the number of rejected blocks is geometric with parameter $a$ and the accepted block has the conditional law $\pi$. The capped failure probability is $(1-a)^t$, and replacing the failure event by a fallback moves at most that much mass. The expected number of blocks is $1/a$, each costing $w$ bits. For uniform integers $a = n/2^{\lceil \log_2 n\rceil} > 1/2$.

## Depends on

- [Discrete distribution generating (DDG) tree](ddg-tree.md)
- [Total variation distance between finite measures](../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)
- [Rejection sampling outputs the target law](../../machine-learning/bayesian-inference-and-sampling/rejection-sampling/tsum-rejections-mul-trial.md)

## Proof depends on

- [Discrete distribution generating (DDG) tree](ddg-tree.md)

## Sources

- Donald E. Knuth and Andrew C. Yao, "The Complexity of Nonuniform Random Number Generation", in Algorithms and Complexity: New Directions and Recent Results, Academic Press, 1976.
- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
