# Recurrence for triangular representation numbers

For an integer $k$, let $t_k(n)$ be the
coefficient of $q^n$ in $\psi(q)^k$, where $\psi(q) = \sum_{m \ge 0} q^{m(m+1)/2}$. For $m \ge 1$
let $b_m = \sum_{d \mid m,\ m/d \text{ odd}} 1/d - \sum_{d \mid m,\ m/d \text{ even}} 1/d$, the
coefficient of $q^m$ in $\log \psi(q)$. Then for every integer $k$ and natural number $n$,

$$t_k(n + 1) = \sum_{j=0}^{n} \frac{k (j + 1)\, b_{j+1}}{n + 1}\, t_k(n - j).$$

## Sources

- Alegri and Christopher, *On Formulas, Recurrences, and Congruences for Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS 26 (2026), Article A93, Corollary 1, second recurrence.
