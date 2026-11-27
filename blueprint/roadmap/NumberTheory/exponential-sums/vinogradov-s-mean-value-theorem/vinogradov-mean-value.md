# Vinogradov's mean value theorem

For all natural numbers $s$ and $k$ and every real
$\varepsilon > 0$ there is a constant $C$ such that
$J_{s,k}(X) \le C (X^{s + \varepsilon} + X^{2s - k(k+1)/2 + \varepsilon})$ for all sufficiently
large natural numbers $X$, where $J_{s,k}(X)$ is the number of pairs of tuples
$(x_1, \dots, x_s)$ and $(y_1, \dots, y_s)$ of integers in $\{1, \dots, X\}$ with
$x_1^j + \dots + x_s^j = y_1^j + \dots + y_s^j$ for every natural number $j \le k$.

## Sources

- J. Bourgain, C. Demeter, and L. Guth, `Proof of the main conjecture in Vinogradov's Mean Value Theorem for degrees higher than three`, Ann. of Math. 184 (2) 2016, 633–682; T. D. Wooley, `Nested efficient congruencing and relatives of Vinogradov's mean value theorem`, Proc. London Math. Soc. 118 (4) 2019, 942–1016. Problem `vinogradov_mean_value` of the lean-eval benchmark.
