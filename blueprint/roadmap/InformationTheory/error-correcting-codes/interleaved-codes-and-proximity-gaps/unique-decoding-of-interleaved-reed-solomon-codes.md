# Unique decoding of interleaved Reed-Solomon codes by row-wise Berlekamp-Welch

Let $\mathrm{RS}_k \subseteq \mathbb{F}^n$ be the Reed-Solomon code of polynomials of degree less than $k$ at distinct points, and suppose $2e + k \le n$. For every received matrix $W$ with rows indexed by a finite set $\kappa$, at most one interleaved codeword (every row in $\mathrm{RS}_k$) lies within column Hamming distance $e$ of $W$. The decoder that runs the Berlekamp-Welch decoder with error bound $e$ on each row and then checks that the decoded rows disagree with $W$ on at most $e$ columns in total returns that codeword when it exists and reports failure otherwise.

## Proof sketch

Two interleaved codewords within column distance $e$ of $W$ differ in at most $2e < n - k + 1$ columns, and every row of their difference is a Reed-Solomon codeword, so all rows vanish by the minimum distance $n - k + 1$. If a close codeword exists, each row of $W$ is within $e$ of the corresponding row, which Berlekamp-Welch recovers; the joint column check then rejects exactly the spurious outputs.

## Depends on

- [Interleaved linear codes](interleaved-linear-code.md)
- [Reed-Solomon code](../reed-solomon-codes/code.md)

## Proof depends on

- [Berlekamp-Welch decoder](../reed-solomon-codes/decode.md)
- [Berlekamp-Welch corrects every error of weight at most $\lfloor (n-k)/2 \rfloor$](../reed-solomon-codes/decode-encode-add.md)
- [Reed-Solomon codes are MDS](../reed-solomon-codes/min-dist-code.md)

## Sources

- L. R. Welch, E. R. Berlekamp, "Error Correction for Algebraic Block Codes", U.S. Patent 4,633,470, 1986.
- E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, "Proximity Gaps for Reed-Solomon Codes", Journal of the ACM, 2023.
