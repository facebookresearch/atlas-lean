# Reed-Solomon codes are MDS

Let $F$ be a field (not necessarily finite), let
$\alpha_0, \dots, \alpha_{n-1} \in F$ be pairwise distinct and let $1 \le k \le n$. The
Reed-Solomon code of the points $\alpha$ with parameter $k$ has minimum distance exactly
$n - k + 1$.

The lower bound counts roots; the upper bound is attained by the encoding of
$\prod_{j < k - 1} (X - \alpha_j)$.

## Background

- [Singleton bound](../bounds-on-code-size/singleton-bound.md): a code is *maximum distance separable* (MDS) when it meets this bound with equality (Guruswami, Rudra and Sudan, *Essential Coding Theory*, draft of August 26, 2025, Definition 5.3.1).
