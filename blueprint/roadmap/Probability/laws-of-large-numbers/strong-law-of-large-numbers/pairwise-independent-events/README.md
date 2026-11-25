# Strong law for pairwise independent events

Let $A_1, A_2, \dots$ be pairwise independent events in a probability space with $\sum_n P(A_n) = \infty$, and let $S_n = \sum_{i=1}^n \mathbf{1}_{A_i}$ count how many of the first $n$ events occur. Then almost surely $S_n / \mathbb{E}[S_n] \to 1$ as $n \to \infty$, where $\mathbb{E}[S_n] = \sum_{i=1}^n P(A_i)$.

## Idea

The second Borel–Cantelli lemma says that infinitely many of the events occur when they are independent and their probabilities have infinite sum. This result sharpens it in two ways: pairwise independence suffices, and the number of occurrences grows like its mean. Pairwise independence makes the indicators uncorrelated, so $\operatorname{Var}(S_n) \le \mathbb{E}[S_n]$, and Chebyshev's inequality bounds $P(|S_n - \mathbb{E}[S_n]| > \varepsilon \mathbb{E}[S_n])$ by $1/(\varepsilon^2 \mathbb{E}[S_n])$. These bounds tend to zero but need not be summable, so one first works along the times $n_k$ at which $\mathbb{E}[S_n]$ first reaches $(k+1)^2$; there the bounds are summable and the first Borel–Cantelli lemma gives convergence. Since $S_n$ and $\mathbb{E}[S_n]$ are nondecreasing and the ratio of consecutive means along the subsequence tends to $1$, bracketing each $n$ between two such times finishes the proof.

## Statements

- [Pairwise-independent strong law for indicator sums](pairwise-indep-slln.md)
- [Quadratic subsequence for the pairwise-independent strong law](slln-subseq.md): definition of the subsequence used in the proof
- [Indices of the quadratic subsequence are positive](slln-subseq-pos.md): lemma used in the proof of the main statement
- [Lower bound on the expected count along the quadratic subsequence](slln-subseq-spec.md): lemma used in the proof of the main statement
- [The quadratic subsequence is strictly increasing](slln-subseq-strict-mono.md): lemma used in the proof of the main statement
- [Chebyshev bound along the subsequence](chebyshev-subseq-bound.md): lemma used in the proof: Chebyshev bound along the subsequence
- [Summable deviation probabilities along the quadratic subsequence](summable-chebyshev-subseq.md): lemma used in the proof: Borel–Cantelli along the subsequence
- [Monotonicity of the expected partial sums](es-mono.md): lemma used in the proof of the main statement
- [The expected partial sums grow by at most one per step](es-step-le-one.md): lemma used in the proof of the main statement
- [Divergent total probability makes the expected partial sums diverge](es-tendsto-at-top.md): lemma used in the proof of the main statement
- [The expected partial sums along the subsequence are positive](es-slln-subseq-pos.md): lemma used in the proof of the main statement
- [Upper bound for the expected partial sums along the subsequence](es-slln-subseq-upper-bound.md): lemma used in the proof of the main statement
- [Ratios of consecutive subsequence expectations tend to one](es-subseq-ratio-tendsto-one.md): lemma used in the proof of the main statement
- [Bracketing by a strictly increasing sequence](exists-bracket-of-strict-mono.md): lemma used in the proof: interpolation between subsequence terms
- [Almost sure convergence from shrinking tail bounds](ae-tendsto-of-ae-eventually-abs-sub-lt.md): lemma used in the proof of the main statement

## Background

- [Partial sums of indicators](../indicator-sums/README.md)
