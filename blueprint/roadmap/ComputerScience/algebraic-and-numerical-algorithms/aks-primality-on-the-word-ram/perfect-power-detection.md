# Perfect-power detection by integer roots

An integer $n \ge 2$ is a **perfect power** if $n = a^b$ for integers $a \ge 2$, $b \ge 2$. Then $b \le \lfloor \log_2 n \rfloor$, and $n$ is a perfect power if and only if there is $b$ with $2 \le b \le \lfloor \log_2 n \rfloor$ and $\lfloor n^{1/b} \rfloor^b = n$. Consequently perfect powers can be recognized with $O(\log n)$ integer $b$-th root computations, each by binary search with $O(\log n)$ trial powerings, for a total of $(\log n)^{O(1)}$ word operations on numbers of $O(\log n)$ bits.

## Proof sketch

If $n = a^b$ with $a \ge 2$ then $2^b \le n$. For fixed $b$ the map $t \mapsto t^b$ is strictly increasing, so $n$ is a $b$-th power exactly when its integer $b$-th root raised to the $b$-th power returns $n$.

## Sources

- M. Agrawal, N. Kayal and N. Saxena, "PRIMES is in P", Annals of Mathematics 160(2), 2004.
