# Hannenhalli–Pevzner formula for the signed reversal distance

For a signed permutation $\pi$ of $\{1, \dots, n\}$, framed by $0$ and $n + 1$, let $d(\pi)$ be its reversal distance, the minimum number of reversals of signed segments transforming $\pi$ into the identity. Replace each element $+x$ by $2x - 1, 2x$ and each $-x$ by $2x, 2x - 1$ to obtain the unsigned image of $\pi$, whose breakpoint graph $G(\pi)$ has all degrees at most $2$, so that its decomposition into alternating cycles is unique. Let $b(\pi)$ be the number of breakpoints, $c(\pi)$ the number of cycles, and $h(\pi)$ the number of hurdles, the unoriented components of the interleaving graph that are minimal for containment of their extents, together with the greatest unoriented component when it does not separate two other hurdles; a fortress is a permutation with an odd number of hurdles, all of them superhurdles. Hannenhalli and Pevzner (1999, Theorem 5) prove

$$d(\pi) = \begin{cases} b(\pi) - c(\pi) + h(\pi) + 1 & \text{if } \pi \text{ is a fortress},\\ b(\pi) - c(\pi) + h(\pi) & \text{otherwise}, \end{cases}$$

The lower bound $d(\pi) \ge b(\pi) - c(\pi) + h(\pi)$ (Theorem 1) uses the fact, due to Bafna and Pevzner, that one reversal decreases $b - c$ by at most $1$.

## Expansion

1. Definitions: signed permutations, reversals, the unsigned image, the breakpoint graph and its unique alternating cycle decomposition, breakpoints and adjacencies.
2. The lower bound $b - c$ from the change of $b - c$ under one reversal, and Theorem 1 with hurdles.
3. Oriented and unoriented components, hurdles, superhurdles and fortresses (Section 7), and the extra reversal needed for fortresses.
4. The matching upper bound: safe paddings (Theorems 2–3), safe reversals in oriented components (Theorem 4), and hurdle merging and cutting (Lemmas 14–21), giving Theorem 5. The algorithm is [polynomial-time optimal sorting of signed permutations by reversals](polynomial-time-optimal-sorting-of-signed-permutations-by-reversals.md).
5. Related distances: the [double-cut-and-join distance formula](../../../Biology/bioinformatics/genome-rearrangements/double-cut-and-join-distance-formula.md) and the [greedy breakpoint algorithm for sorting by reversals](../../../Biology/bioinformatics/genome-rearrangements/greedy-breakpoint-bound-for-unsigned-sorting-by-reversals.md).

## Sources

- S. Hannenhalli and P. A. Pevzner, Transforming cabbage into turnip: polynomial algorithm for sorting signed permutations by reversals, J. ACM 46 (1999), 1–27, Theorems 1 and 5. <https://doi.org/10.1145/300515.300516>
