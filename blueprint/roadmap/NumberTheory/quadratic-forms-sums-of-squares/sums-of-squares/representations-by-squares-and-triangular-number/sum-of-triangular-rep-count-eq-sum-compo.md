# Composition formula for triangular representation numbers

For an integer $k$, let $t_k(n)$
be the coefficient of $q^n$ in $\psi(q)^k$, where $\psi(q) = \sum_{m \ge 0} q^{m(m+1)/2}$. For
$m \ge 1$ let
$b_m = \sum_{d \mid m,\ m/d \text{ odd}} 1/d - \sum_{d \mid m,\ m/d \text{ even}} 1/d$, the
coefficient of $q^m$ in $\log \psi(q)$. Then for every integer $k$ and natural number $n$,

$$t_k(n) = \sum_{(w_1, \dots, w_l)} \frac{k^l}{l!}\, b_{w_1} \cdots b_{w_l},$$

where the sum runs over all compositions $(w_1, \dots, w_l)$ of $n$, that is, all tuples of positive
integers with sum $n$, of every length $l$ (for $n = 0$, only the empty composition).

The source prints $b_m$ with the parity condition on $d$ instead of $m/d$; with that coefficient the
formula fails, giving $t_1(2) = 1$ although $t_1(2) = 0$.

## Sources

- Alegri and Christopher, *On Formulas, Recurrences, and Congruences for Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS 26 (2026), Article A93, Theorem 2 (`integers-2026-A93-thm-2`).
