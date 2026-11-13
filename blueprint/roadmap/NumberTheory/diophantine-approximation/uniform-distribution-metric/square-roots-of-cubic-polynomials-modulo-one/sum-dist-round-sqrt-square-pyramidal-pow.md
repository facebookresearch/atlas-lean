# Power sums of the distance from the square root of a square pyramidal number to the nearest integer

**Power sums of the distance from the square root of a square pyramidal number to the nearest
integer.** Let $P_n$ be the $n$-th square pyramidal number and write
$\|x\| = |x - \operatorname{round}(x)|$ for the distance from a real $x$ to the nearest integer.
For every positive integer $k$ there is a real constant $C_k$ such that for every real $t \ge 1$,

$$\Bigl|\sum_{1 \le n \le t} \|\sqrt{P_n}\|^k - \frac{t}{2^k (k + 1)}\Bigr| \le C_k t^{3/4},$$

that is, with $\mu_k = 1/(2^k (k + 1))$ and $G_k(t) = \sum_{1 \le n \le t} \|\sqrt{P_n}\|^k$,
one has $G_k(t) = \mu_k t + O_k(t^{3/4})$.

The source writes $h(n) = \sqrt{n(n+1)(2n+1)/6}$, which is $\sqrt{P_n}$.

## Sources

- Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29 (2026), Article 26.5.5, Lemma 11 (`jis-2026-26.5.5-lem-11`).
