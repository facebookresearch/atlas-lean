# Log-balancedness of the n-th roots of generalized Leonardo numbers

Let $k \ge 1$ be an
integer, let $L_{k,n}$ be the generalized Leonardo numbers, and let $n_k$ be an integer with
$n_k \ge 9$ and $n_k \ge (1 + \sqrt{64k - 7})/4$. Then for every integer $n \ge n_k + 1$,

$$\left(L_{k,n}^{1/n}\right)^2 \le L_{k,n-1}^{1/(n-1)} L_{k,n+1}^{1/(n+1)}$$

and

$$\frac{L_{k,n-1}^{1/(n-1)}}{(n-1)!} \cdot \frac{L_{k,n+1}^{1/(n+1)}}{(n+1)!} \le
\left(\frac{L_{k,n}^{1/n}}{n!}\right)^2;$$

that is, the sequence $(L_{k,n}^{1/n})_{n \ge n_k}$ is log-balanced (Došlić): it is log-convex
and its quotient by $n!$ is log-concave.

The paper asserts only that some $n_k \ge \max\{9, (1 + \sqrt{64k - 7})/4\}$ with this property
exists; the statement above gives the threshold its proof establishes (log-concavity of
$L_{k,n}^{1/n}/n!$ once $n \ge (1 + \sqrt{64k - 7})/4$, log-convexity of $L_{k,n}^{1/n}$ from
$n = 9$ on).

## Sources

- Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Theorem 4 (`integers-2024-A82-thm-4`).
