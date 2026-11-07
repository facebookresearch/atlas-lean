# The (p, q)-deformed Spivey formula

Let $p$ and $q$ be real numbers with
$0 < q < p \le 1$, and for $k \in \mathbb{N}$ put $[k] = (p^k - q^k)/(p - q)$. Define real numbers
$S(n, k)$ for $n, k \in \mathbb{N}$ by $S(0, 0) = 1$, $S(0, k) = 0$ for $k \ge 1$,
$S(n + 1, 0) = 0$, and, for $k \ge 1$,
$S(n + 1, k) = p^{n + 1 - k} q^{k - 1} S(n, k - 1) + [k] \, S(n, k)$, where the exponent
$n + 1 - k$ is read as $0$ when $k > n + 1$. Put $\tilde S(n, k) = p^{\binom{k}{2}} S(n, k)$ and
$\tilde B_n(x) = \sum_{k=0}^{n} \tilde S(n, k) \, x^k$ for real $x$. Then for all
$m, n \in \mathbb{N}$,

$$\tilde B_{n+m}(1) = \sum_{k=0}^{m} \sum_{j=0}^{n} \binom{n}{j} \tilde S(m, k) \, [k]^{n-j} \,
q^{jk} \, \tilde B_j\bigl(p^{n+m-j}\bigr),$$

with $0^0 = 1$.

Proof: We formalize the operator proof around equations `eq1`, `eq2'`, `eq4`, `meq`,
`pqexpn`, and `lasteq` in Oussi's paper, using formal power series in place of convergent series.

## Sources

- L. Oussi, *A (p,q)-Deformed Recurrence for the Bell Numbers*, Journal of Integer Sequences 23 (2020), Article 20.5.2, main theorem equation `lasteq`, lines 214-220, <https://cs.uwaterloo.ca/journals/JIS/VOL23/Oussi/oussi5.tex>.
