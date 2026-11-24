# Bowman's formula for cyclic compositions with a part count in a residue class

Let $A \subseteq \mathbb{N}$ and let $j_A(x) = \sum_{a \in A,\, a \ge 1} x^a \in \mathbb{Q}[[x]]$ and $L_{m,s}(y) = \sum_{r \ge 1,\ r \bmod m = s \bmod m} y^r / r \in \mathbb{Q}[[y]]$. Let $d_A(m, q; n)$ be the number of cyclic compositions of $n$ (nonempty compositions up to cyclic rotation) with all parts in $A$ and a number of parts congruent to $q$ modulo $m$, and let $\varphi$ be Euler's totient function. For all natural numbers $m$, $q$ and $n$ with $q < m$,

$$d_A(m, q; n) = \sum_{k \mid n} \; \sum_{\substack{0 \le s < m \\ ks \bmod m \,=\, q}} \frac{\varphi(k)}{k}\, [x^{n/k}]\, L_{m,s}\bigl(j_A(x)\bigr),$$

in $\mathbb{Q}$, where $k$ runs over the positive divisors of $n$ and $L_{m,s}(j_A(x))$ is the substitution of $j_A(x)$, a series with constant term $0$, into $L_{m,s}$. For $n = 0$ the sum over divisors is empty and both sides are $0$. The $k$-th term is the coefficient of $x^n$ in $L_{m,s}(j_A(x^k))$, so the identity is the coefficient form of $\sum_n d_A(m, q; n) x^n = \sum_{k \ge 1} \sum_{0 \le s < m,\ ks \equiv q} \frac{\varphi(k)}{k} L_{m,s}(j_A(x^k))$.

## Sources

- Joshua P. Bowman, *Compositions with an Odd Number of Parts, and Other Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6, Theorem 3.
