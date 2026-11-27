# Large valuations in short runs of consecutive integers are rare

For a natural number
$x$ let $K = \lfloor \exp(0.8 \sqrt{\log x}) \rfloor$ and, for a prime $p$, let
$D_p = 1 + \lfloor \log x / \log p \rfloor$. Write $v_p(n)$ for the exponent of $p$ in a
positive integer $n$. Then the number of integers $m$ with $1 \le m \le x$ for which some prime
$p < 2K$ satisfies $\max \{ v_p(m + i) : 1 \le i \le K \} > D_p / \log D_p$ is $o(x)$ as
$x \to \infty$.

For large $x$ every prime $p < 2K$ is at most $x$, so $D_p \ge 2$ and $\log D_p > 0$.

## Sources

- Carl Pomerance, *Remarks on the Middle Binomial Coefficient*, INTEGERS 26 (2026), Article A47, Lemma 5.
