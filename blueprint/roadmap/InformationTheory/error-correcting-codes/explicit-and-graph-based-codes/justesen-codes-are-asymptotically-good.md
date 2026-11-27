# Distance of Justesen codes; Justesen codes are asymptotically good

For a field with $q = 2^b$ elements and every $r \ge 0$, the Justesen code of outer dimension $K$ has minimum distance at least

$$\Bigl(q - K - \sum_{j=0}^{r} \binom{2b}{j}\Bigr)(r + 1).$$

For $b = 16 s$ with $s \ge 1$ and $K = 2^{16 s - 1}$, the code is a binary code of length $n = 32 s (2^{16 s} - 1)$, rate $q/(4(q - 1)) > 1/4$ (with $q = 2^{16 s}$), and minimum distance $d$ with $n \le 128 d$. Hence the Justesen codes form an explicit asymptotically good family of binary codes: lengths tend to infinity while rate and relative distance stay bounded below by positive constants.

## Proof sketch

A nonzero outer codeword has at least $q - K$ nonzero positions, and their inner encodings are pairwise distinct nonzero words of length $2b$. At most $\sum_{j \le r}\binom{2b}{j}$ of them have weight at most $r$, so the remaining ones each contribute weight at least $r + 1$. With $b = 16s$ and $r = s$, the binomial sum is at most $2^{16 s - 2}$, giving $n \le 128 d$.

## Depends on

- [Wozencraft encodings and Justesen codes](justesen-code.md)
- [Minimum distance](../linear-codes/min-dist.md)

## Proof depends on

- [Reed-Solomon codes are MDS](../reed-solomon-codes/min-dist-code.md)
- [Good family of codes](../locally-testable-codes/is-good.md)

## Sources

- J. Justesen, "Class of Constructive Asymptotically Good Algebraic Codes", IEEE Transactions on Information Theory, 1972.
- V. Guruswami, A. Rudra, M. Sudan, "Essential Coding Theory", draft book, 2019.
