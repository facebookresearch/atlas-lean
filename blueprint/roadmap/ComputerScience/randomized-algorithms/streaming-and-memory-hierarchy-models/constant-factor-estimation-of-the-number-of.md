# Constant-factor estimation of the number of distinct elements

Let $x_1, \dots, x_m$ be a nonempty stream of elements of $\{1, \dots, n\}$, $n \ge 2$, and let $F_0 \ge 1$ be the number of distinct elements, the number of values with positive frequency. For every $c > 2$ there is a one-pass streaming algorithm that uses $O(\log n)$ bits and outputs an estimate $Y$ with $\Pr[Y/F_0 \notin [1/c, c]] \le 2/c$. The algorithm takes $d$ the least integer with $2^d > n$, identifies $\{1, \dots, n\}$ with elements of $\mathrm{GF}(2^d)$ by the binary expansion, writing each field element in a fixed polynomial basis as a $d$-bit string, picks uniformly random $a, b \in \mathrm{GF}(2^d)$ and the hash $h(x) = ax + b$, lets $r(z)$ be the number of trailing zero bits of the $d$-bit string of $z$ with $r(0) = d$, keeps $R = \max_i r(h(x_i))$, and outputs $Y = 2^R$.

## Depends on

- [Frequency of an element in a stream](../frequency-moments-of-data-streams/freq.md)

## Sources

- N. Alon, Y. Matias and M. Szegedy, "The space complexity of approximating the frequency moments", *Journal of Computer and System Sciences* 58(1):137–147, 1999, Proposition 2.3
