# Expansion of the (q, r)-Dowling polynomial in q-Stirling numbers

Let
$m, r, q, x \in \mathbb{C}$ and $n \in \mathbb{N}$, and write $[k + 1]_q = 1 + q + \dots + q^k$.
Let $S$ be a complex-valued function on pairs of natural numbers satisfying the recurrence of the
$q$-Stirling numbers of the second kind: for all $a, k \in \mathbb{N}$, $S(0, 0) = 1$,
$S(0, k + 1) = 0$, $S(a + 1, 0) = 0$ and $S(a + 1, k + 1) = q^k S(a, k) + [k + 1]_q \, S(a, k + 1)$.
Let $W_{m,r,q}$ be the $(q, r)$-Whitney numbers of the second kind, and let $D_n(x)$ be the
value at $x$ of the $(q, r)$-Dowling polynomial $\sum_{k=0}^{n} W_{m,r,q}(n, k) \, X^k$. Then

$$D_n(x) = \sum_{k=0}^{n} \binom{n}{k} r^{n-k} \sum_{j=0}^{k} m^{k-j} S(k, j) \, x^j.$$

## Sources

- M. M. Mangontarum, *Some Theorems and Applications of the (q,r)-Whitney Numbers*, Journal of Integer Sequences 20 (2017), Article 17.2.5, theorem equation `genpriv`, lines 782-789, <https://cs.uwaterloo.ca/journals/JIS/VOL20/Mangontarum/mango4.tex>.
