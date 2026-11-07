# The $\pm 1$ paperfolding Dirichlet series at odd integers

Let $(f_n)_{n \ge 0}$ be the
regular paperfolding sequence, indexed from $0$, and let $E_{2k}$ be the even-index Euler number.
For every integer $k \ge 1$,

$$
\sum_{n \ge 0} \frac{(-1)^{f_n}}{(n+1)^{2k+1}} =
\frac{\pi^{2k+1} |E_{2k}|}{(2^{2k+2} - 2)(2k)!}.
$$

In the source's indexing $b_n = f_{n-1}$ for $n \ge 1$, this is the sum over $n \ge 1$ of
$(-1)^{b_n}/n^{2k+1}$. The source prints the sum as $\sum_{n \ge 0} (-1)^{b_n}/(n+1)^{2k+1}$,
which uses $b_0$, left undetermined by the recurrence $b_{2n} = b_n$; its proof (from Lemma 5)
gives the sum over $n \ge 1$ stated here.

## Sources

- László Tóth, *Evaluating ζ(s) at Odd Positive Integers Using Automatic Dirichlet Series*, Journal of Integer Sequences 28 (2025), Article 25.4.4, Corollary 7 (`jis-2025-25.4.4-cor-7`); `bₙ` read from arXiv:2508.04151v1.
