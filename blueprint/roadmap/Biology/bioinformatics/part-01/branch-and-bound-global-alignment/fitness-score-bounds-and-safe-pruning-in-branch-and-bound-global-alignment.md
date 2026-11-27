# Fitness-score bounds and safe pruning in branch-and-bound global alignment

Let $S_1$ and $S_2$ have lengths $m$ and $n$, and score a global alignment with match score $M > 0$, mismatch score $M_s < M$ and linear gap score $G < 0$. A node of the search tree is a partial alignment of the prefixes $S_1[1..P_1]$ and $S_2[1..P_2]$ with present score $\mathrm{PrS}$; each node has at most three children (match/mismatch, gap in $S_2$, gap in $S_1$). With remaining lengths $x_1 = m - P_1$, $x_2 = n - P_2$, put $x = \min(x_1, x_2)$ and $y = |x_1 - x_2|$ and define the future-score bounds and fitness interval

$$F_{\max} = xM + yG, \qquad F_{\min} = xM_s + yG, \qquad [T_{\max}, T_{\min}] = [\mathrm{PrS} + F_{\max},\ \mathrm{PrS} + F_{\min}].$$

Then, for a node with interval $[T_{\max}, T_{\min}]$:

1. a match child has interval $[T_{\max},\ T_{\min} + (M - M_s)]$;
2. a mismatch child has interval $[T_{\max} + (M_s - M),\ T_{\min}]$;
3. a gap child has interval $[T_{\max}, T_{\min}]$ (gap that shrinks the length difference) or $[T_{\max} + (2G - M),\ T_{\min} + (2G - M_s)]$ (gap that widens it);
4. hence a match child, or a gap child that inserts the gap into the sequence with the shorter remaining suffix, always has the largest $T_{\max}$ among the children.

Expanding nodes best-first by $T_{\max}$ and pruning a branch when (a) another node with the same $(P_1, P_2)$ has a strictly larger present score, or (b) its $T_{\max}$ does not exceed the best complete alignment score found so far, never discards every optimal alignment, so the search returns an optimal alignment (one with the Needleman–Wunsch optimum score).

## Depends on

- [The table computes the optimal global alignment score](../../sequence-alignment/pairwise-sequence-alignment/nw-tab-eq-nw-score.md)

## Expansion

Any completion of a node aligns some $a \le x$ residue pairs, each scoring at most $M$, and places $x_1 + x_2 - 2a = 2x + y - 2a$ gaps, so its future score is at most $aM + (2x+y-2a)G = F_{\max} - (x-a)(M-2G) \le F_{\max}$; thus $T_{\max}$ is an upper bound on every completion's score (an admissible bound in the sense of best-first search). This step and item 4 use $M \ge 2G$, which follows from $M > 0 > G$ (the source assumes $M > 0$, $M_s < 0$, $G < 0$); without it they fail, e.g. for $M = -3$, $M_s = -4$, $G = -1$ and $S_1 = S_2 = \mathtt A$ the two-gap alignment scores $-2 > T_{\max} = -3$. The child formulas follow by updating $\mathrm{PrS}$ by $M$, $M_s$ or $G$ and recomputing $x$ and $y$. Rule (a) is the dynamic-programming principle that only the best prefix alignment ending at a cell matters; rule (b) discards nodes whose upper bound cannot beat a known solution. The method is exact; its speed-up over the quadratic table comes from pruning when the sequences are similar.

## Sources

- A. Chakraborty and S. Bandyopadhyay, "FOGSAA: Fast Optimal Global Sequence Alignment Algorithm", Scientific Reports 3 (2013) 1746, <https://doi.org/10.1038/srep01746>, PMCID PMC3638164. Definitions of Present, Future and Fitness Scores; Lemmas 1–4 and Corollary 1.
