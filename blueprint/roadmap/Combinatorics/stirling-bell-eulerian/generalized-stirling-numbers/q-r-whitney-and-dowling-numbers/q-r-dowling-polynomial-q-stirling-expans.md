# (q, r)-Dowling polynomial expansion from the defining recurrences

Let
$q, m, r, x \in \mathbb{C}$ and $n \in \mathbb{N}$, and write $[k + 1]_q = \sum_{i=0}^{k} q^i$.
Let $S$ and $W$ be complex-valued functions on pairs of natural numbers, and let $D(a, y)$ be a
complex-valued function of $a \in \mathbb{N}$ and $y \in \mathbb{C}$, such that for all
$a, k \in \mathbb{N}$ and $y \in \mathbb{C}$: $S(0, 0) = 1$, $S(0, k + 1) = 0$, $S(a + 1, 0) = 0$
and $S(a + 1, k + 1) = q^k S(a, k) + [k + 1]_q \, S(a, k + 1)$ (the recurrence of the
$q$-Stirling numbers of the second kind); $W(0, 0) = 1$, $W(0, k + 1) = 0$,
$W(a + 1, 0) = r^{a + 1}$ and $W(a + 1, k + 1) = q^k W(a, k) + (m [k + 1]_q + r) \, W(a, k + 1)$
(the recurrence of the $(q, r)$-Whitney numbers of the second kind); and
$D(a, y) = \sum_{k=0}^{a} W(a, k) \, y^k$ (the $(q, r)$-Dowling polynomial). Then

$$D(n, x) = \sum_{k=0}^{n} \binom{n}{k} r^{n-k} \sum_{j=0}^{k} m^{k-j} S(k, j) \, x^j.$$

## Sources

- M. M. Mangontarum, *Some Theorems and Applications of the (q,r)-Whitney Numbers*, Journal of Integer Sequences 20 (2017), Article 17.2.5, theorem equation `genpriv`, lines 782-789, <https://cs.uwaterloo.ca/journals/JIS/VOL20/Mangontarum/mango4.tex>.
