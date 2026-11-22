# The distance from the square root of a square pyramidal number to the nearest integer is uniformly distributed

**The distance from the square root of a square pyramidal number to the nearest integer is
uniformly distributed.** Let $P_n$ be the $n$-th square pyramidal number, write
$\|x\| = |x - \operatorname{round}(x)|$ for the distance from a real $x$ to the nearest integer,
and let $(y_n)_{n \ge 0}$ be natural numbers such that $|P_n - y_n^2| \le |P_n - z^2|$ for all
natural numbers $n$ and $z$ (so $y_n^2$ is a square nearest to $P_n$). Put
$d_n = |\sqrt{P_n} - y_n|$. Then $d_n = \|\sqrt{P_n}\|$ and $d_n \le 1/2$ for every $n \ge 0$,
and $(d_n)_{n \ge 1}$ is uniformly distributed in $[0, 1/2]$: for all real $\alpha, \beta$ with
$0 \le \alpha < \beta \le 1/2$,

$$\lim_{N \to \infty} \frac{1}{N}
\#\{1 \le n \le N : \alpha \le d_n \le \beta\} = 2(\beta - \alpha).$$

The source shows that $y_n$ is unique, and takes the limit over real $x \to \infty$, which is
equivalent to the limit along integers $N$.

## Sources

- Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29 (2026), Article 26.5.5, Proposition 9 (`jis-2026-26.5.5-prop-9`).
