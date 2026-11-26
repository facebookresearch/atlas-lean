# Binary linear codes beat the Gilbert-Varshamov bound by a linear factor (Saglam)

For every $0 < \varepsilon < 1/2$ there are constants $c > 0$, $K$ and $N$ such that for all $n \ge N$ and all integers $d$ with $K \log_2 n \le d \le (1/2 - \varepsilon) n$ there is a binary linear code of length $n$ (the kernel of a parity-check matrix over $\mathbb{F}_2$) with minimum distance at least $d$ and

$$|C| \cdot \sum_{1 \le i < d} \binom{n}{i} \ge c\, n\, 2^n,$$

that is, $\Omega(n)$ times the Gilbert-Varshamov bound $2^n / (V + 1)$.

## Proof sketch

A finite set $B$ of vectors over $\mathbb{F}_2$ none of whose zero-sum subsets has odd size can be mapped to $1$ by one extra parity check, and it suffices that $B$ contain no odd zero-sum circuit; a circuit of size $s$ spans dimension at least $s - 1$. Character orthogonality counts zero-sum tuples in the punctured Hamming ball $B$ through its Fourier transform, and summing over odd sizes against the series of $\sinh z - z$ bounds the weighted number of odd circuits. The moment and tail estimates for the Fourier transform of the punctured ball, which follow from bounds of Kirshner and Samorodnitsky on low-degree polynomials on the cube, make this count small enough that random parity checks plus one extra check save a factor $\Omega(n)$.

## Depends on

- [Code with a given parity-check matrix](../linear-codes/of-parity-check.md)
- [Minimum distance](../linear-codes/min-dist.md)

## Proof depends on

- [Gilbert–Varshamov bound, rate form](../bounds-on-code-size/exists-code-exp-le-card.md)
- [Gilbert–Varshamov bound for linear codes](../bounds-on-code-size/exists-linear-code-finrank-eq.md)

## Sources

- M. Saglam, "Linear Codes Exceeding the Gilbert-Varshamov Bound", preprint, 2026.
- N. Kirshner, A. Samorodnitsky, "A Moment Ratio Bound for Polynomials and Some Extremal Properties of Krawtchouk Polynomials and Hamming Spheres", IEEE Transactions on Information Theory, 2021.
