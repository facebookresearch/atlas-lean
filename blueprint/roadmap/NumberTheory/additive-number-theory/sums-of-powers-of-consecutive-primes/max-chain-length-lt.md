# Upper bound for the maximal gleeful chain length

Let $p_1 = 2, p_2 = 3, \dots$ be the
primes in increasing order. Let $k > 1$, $M_0 \ge 6$, $M \ge M_0$ and $x$ be natural numbers with
$p_1^k + \cdots + p_M^k \le x < p_1^k + \cdots + p_{M+1}^k$. Put $y = M_0$,

$$B = \frac{\log(y+1)}{\log y} + \frac{\log\log((y+1)^2)}{\log y} \cdot \frac{k}{k+1}$$

and $C = (y/(y-1))^{1/(k+1)} B^{k/(k+1)}$, where $\log$ is the natural logarithm. Then

$$M < 4^{1/(k+1)} \cdot \frac{(k+1)\, x^{1/(k+1)}}{(\log x)^{k/(k+1)}} \cdot C.$$

## Sources

- Sara Moore and Jonathan P. Sorenson, *Explicit Bounds and Parallel Algorithms for Counting Multiply Gleeful Numbers*, INTEGERS 26 (2026), Article A84, Lemma 1, with `B`, `C` from Section 2.
