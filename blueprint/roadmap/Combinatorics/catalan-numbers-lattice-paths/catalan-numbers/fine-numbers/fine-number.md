# Fine numbers

For a natural number $n$, the Fine number $F(n)$, indexed from $0$ so
that $F(0) = 1$, is the rational number

$$F(n) = \frac{1}{n+1} \sum_{i=0}^{n} (-2)^i \, (i+1) \binom{2(n+1)}{n-i}.$$

## Sources

- Fine numbers (OEIS A000957), zero-based: `fineNumber n` is source `𝔽_(n+1)`. Source explicit formula `𝔽_n = (1/n) * ∑_{i=1}^n (-2)^(i-1) * i * C(2n, n-i)` with `𝔽_1 = 1`, from JIS VOL21/Janjic3/janjic96.tex lines 105-108 and 157-158. <https://cs.uwaterloo.ca/journals/JIS/VOL21/Janjic3/janjic96.tex>.
