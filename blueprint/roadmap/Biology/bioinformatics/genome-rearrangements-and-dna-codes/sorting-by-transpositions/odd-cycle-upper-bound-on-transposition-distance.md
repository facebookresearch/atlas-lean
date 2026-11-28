# Odd-cycle upper bound on the transposition distance

A *transposition* exchanges two adjacent blocks of a permutation $\pi \in S_n$, modelling the swap of two adjacent gene blocks in a chromosome. The *transposition distance* $d_t(\pi)$ is the least number of transpositions turning $\pi$ into the identity, and the *transposition diameter* is $TD(n) = \max_{\pi \in S_n} d_t(\pi)$. Let $c_{odd}(\pi)$ be the number of odd cycles of the Bafna–Pevzner cycle graph of $\pi$ (the alternating cycles of its breakpoint graph with an odd number of black edges).

**Theorem.** For every $\pi \in S_n$,

$$
\frac{n+1-c_{odd}(\pi)}{2} \;\le\; d_t(\pi) \;\le\; 11 \left\lfloor \frac{n+1-c_{odd}(\pi)}{16} \right\rfloor + \left\lfloor \frac{3\big((n+1-c_{odd}(\pi)) \bmod 16\big)}{4} \right\rfloor .
$$

In particular $TD(n) \le 11 \lfloor n/16 \rfloor + \lfloor 3(n \bmod 16)/4 \rfloor$, and an $O(n^6)$-time algorithm sorts every permutation within a factor $1.375$ of $d_t(\pi)$ without first transforming $\pi$ into a simple permutation.

## Expansion

The lower bound (Bafna and Pevzner) holds because one transposition raises $c_{odd}$ by at most $2$ and the identity has $n+1$ odd cycles. The upper bound encodes $\pi$ algebraically as the even permutation $\sigma\pi^{-1}$ and transpositions as applicable $3$-cycles; a case analysis shows that whenever the norm of $\sigma\pi^{-1}$ is at least $8$ there is a sequence of $11$ transpositions raising $c_{odd}$ by $16$ (an $\tfrac{11}{8}$-sequence), and the remainder is finished with $2$-moves of ratio $\tfrac32$. Dividing the upper bound by the lower bound gives the ratio $11/8 = 1.375$.

## Sources

- L. A. G. Silva, L. A. B. Kowada, N. R. Rocco and M. E. M. T. Walter, *A new 1.375-approximation algorithm for Sorting By Transpositions*, arXiv:2001.11570, Theorems 3, 36, 38 and 39 and Corollary 37. <https://doi.org/10.48550/arXiv.2001.11570> Published version: Algorithms for Molecular Biology 17 (2022) 1, <https://doi.org/10.1186/s13015-022-00205-z>.
