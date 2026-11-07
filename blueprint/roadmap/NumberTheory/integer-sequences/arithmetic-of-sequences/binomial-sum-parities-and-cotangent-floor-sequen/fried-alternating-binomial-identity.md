# Fried's alternating binomial identity

For integers $a$ and $b$ let $\binom{a}{b}$ be the
binomial coefficient when $a, b \ge 0$ (so $0$ when $b > a$), and $0$ when $a < 0$ or $b < 0$.
For natural numbers $n$, $r$, $s$ with $r \le n$ and $s \le 2r$, with all arguments computed in
the integers,

$$\sum_{k=0}^{n} (-1)^k \binom{n}{k} \binom{2n-2r}{n-k} \binom{n-k}{n-2r+s}
\binom{2r-k-s}{n-s} = (-1)^n \binom{n}{2r-n} \binom{2n-2r}{n-s}.$$

## Sources

- Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29 (2026), Article 26.1.8, Lemma 1 (`jis-2026-26.1.8-lem-1`).
