# Two-parameter generalization of Knuth's old sum

For all natural numbers $m$ and $n$ and
every real number $v > -1$,

$$
\sum_{k=0}^{n} \frac{(-1)^k \binom{n}{k}}{2^{k+m}} \binom{2k+2m+v}{(2k+2m+v)/2}
\binom{k+m+v}{v/2}^{-1}
$$

equals, if $n$ is even,

$$
\sum_{k=0}^{\lfloor m/2 \rfloor} \frac{\binom{m}{2k}}{2^{n+2k}} \binom{2k+n}{(2k+n)/2}
\binom{(2k+n+v)/2}{(2k+n)/2}^{-1}
$$

and, if $n$ is odd,

$$
-\sum_{k=1}^{\lfloor (m+1)/2 \rfloor} \frac{\binom{m}{2k-1}}{2^{n+2k-1}}
\binom{2k+n-1}{(2k+n-1)/2} \binom{(2k+n-1+v)/2}{(2k+n-1)/2}^{-1}.
$$

Here $\binom{a}{b} = \Gamma(a+1)/(\Gamma(b+1)\,\Gamma(a-b+1))$ is the generalized binomial
coefficient of complex arguments, which at natural arguments is the ordinary binomial coefficient.

This is equation (14) of the source.

## Sources

- Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related Sums*, INTEGERS 26 (2026), Article A19, Theorem 2 (`integers-2026-A19-thm-2`).
