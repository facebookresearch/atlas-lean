# Bonferroni alpha spending controls the type I error

Let $f$ be an alpha-spending function for level $\alpha \le 1$ ($f(0) = 0$, $f$ nondecreasing on $[0, 1]$, $f(1) \le \alpha$), and $0 = \tau_0 \le \tau_1 \le \dots \le \tau_K \le 1$ information times; look $k$ ($k < K$) is tested at the nominal level $c_k = f(\tau_{k+1}) - f(\tau_k)$. Let the look p-values $p_k$, $k < K$, be valid under the null $P$. Then the probability that some look rejects is at most $\alpha$, whatever the joint law of the looks.

## Sources

- Lan and DeMets (1983); Jennison and Turnbull (2000), Chapter 7.
