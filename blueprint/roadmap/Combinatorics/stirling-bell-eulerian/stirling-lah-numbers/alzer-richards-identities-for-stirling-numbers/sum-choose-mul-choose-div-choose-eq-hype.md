# The Alzer–Richards binomial sum as a ${}_3F_2$ series

Let $m \ge 1$ be an integer and
let $p, x$ be complex numbers with $p \ne -j$ and $x \ne -j$ for every integer $j$ with
$1 \le j \le \lfloor m/2 \rfloor$. Write $\binom{z}{k} = z(z-1)\cdots(z-k+1)/k!$ for complex $z$
and $(z)_n = z(z+1)\cdots(z+n-1)$ for the rising factorial. Then

$$
\sum_{k=0}^{\lfloor m/2 \rfloor} \frac{\binom{m-k}{k} \binom{m+x}{m-k}}{2^{2k} \binom{k+p}{k}} =
\frac{(x+1)_m}{m!} \sum_{n=0}^{\lfloor m/2 \rfloor}
\frac{(-m/2)_n \, ((1-m)/2)_n}{(p+1)_n \, (x+1)_n}.
$$

The sum on the right is the terminating hypergeometric series
${}_3F_2(-m/2, (1-m)/2, 1; p+1, x+1; 1)$, written out up to $n = \lfloor m/2 \rfloor$, beyond
which its terms vanish.

## Sources

- Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 9 (i), Equation (15).
