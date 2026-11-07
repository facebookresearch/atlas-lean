# Partitions with non-negative crank

For a partition $\lambda$, let $\omega(\lambda)$ be the
number of parts equal to $1$. The crank of $\lambda$ is its largest part if $\omega(\lambda) = 0$
(the largest part of the empty partition being $0$), and otherwise the number of parts greater
than $\omega(\lambda)$, counted with multiplicity, minus $\omega(\lambda)$. Let $p(k)$ be the
number of partitions of $k$. Then for every natural number $N$, the number of partitions of $N$
with non-negative crank equals

$$\sum_{n \ge 0,\ n(n+1)/2 \le N} (-1)^n \, p\bigl(N - n(n+1)/2\bigr).$$

This is the coefficient-wise form of the generating function for partitions with non-negative
crank. The source notes this result is originally due to Uncu.

## Sources

- George E. Andrews and David Newman, "The Minimal Excludant in Integer Partitions," Journal of Integer Sequences 23 (2020), Article 20.2.3, Theorem (label Theorem1, equation 1.11), lines 161–165, https://cs.uwaterloo.ca/journals/JIS/VOL23/Andrews/andrews5.tex
