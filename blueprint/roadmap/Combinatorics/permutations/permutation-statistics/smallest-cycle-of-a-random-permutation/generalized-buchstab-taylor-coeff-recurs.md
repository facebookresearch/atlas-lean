# Recursion for the Taylor coefficients of the generalized Buchstab function

Let $K > 0$,
let $\Omega$ be a real function with $\Omega(x) = 1$ for $1 \le x < 2$ and
$\Omega(x) = 1 + K \int_2^x \frac{\Omega(u-1)}{u-1}\,du$ for $x \ge 2$, and let $c_{n,i}$
($n, i \ge 0$) be real numbers such that for every integer $n \ge 1$ and every real $z$ with
$-1 \le z < 1$ the series $\sum_{i \ge 0} c_{n,i} z^i$ converges absolutely to
$\Omega(n + (1+z)/2)$. Then $c_{1,0} = 1$, $c_{1,i} = 0$ for every $i \ge 1$,

$$c_{2,0} = 1 + K \sum_{i \ge 0} \frac{(-1)^i}{(i+1)\,2^{i+1}},$$



$$c_{2,i} = K \sum_{j \ge 0} \frac{(-1)^{j+i-1} \binom{j+i}{i}}{(j+i)\,2^{j+i}} \quad (i \ge 1),$$

and for every $n \ge 3$, writing
$\alpha_{n,m} = \sum_{j=0}^{m} \frac{(-1)^{m-j}}{(2n-1)^{m-j}}\, c_{n-1,j}$ for $m \ge 0$,

$$c_{n,0} = \sum_{i \ge 0} c_{n-1,i} -
\frac{K}{2n-1} \sum_{i \ge 0} \frac{(-1)^{i+1} \alpha_{n,i}}{i+1}$$

and $c_{n,i} = \dfrac{K\, \alpha_{n,i-1}}{(2n-1)\, i}$ for every $i \ge 1$.

Here $c_{2,0} = 1 + K \log(3/2)$. The printed statement of Theorem 4 has
$c_{2,0} = 1 + K \sum_{i \ge 1} 1/(i\, 2^i)$, which omits the sign $(-1)^{i-1}$.

## Sources

- Claude Gravel and Daniel Panario, *Evaluating the Generalized Buchstab Function and Revisiting the Variance of the Distribution of the Smallest Components of Combinatorial Objects*, INTEGERS 24 (2024), Article A7, Theorem 4.
