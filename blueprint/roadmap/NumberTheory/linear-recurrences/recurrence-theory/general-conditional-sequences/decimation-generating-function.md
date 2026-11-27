# Generating function of a decimated linear recurrence

Let $R$ be a commutative ring,
let $m$ and $r$ be natural numbers, and let $(A_j)_{j \ge 0}$ and $(s_n)_{n \ge 0}$ be
sequences in $R$ such that $s_{n+mr} = \sum_{j\lt m} A_j s_{n+jr}$ for all $n \ge 0$. Then, in
the ring $R[[x]]$ of formal power series,

$$
\Bigl(\sum_{n \ge 0} s_n x^n\Bigr)\Bigl(1 - \sum_{j\lt m} A_j x^{(m-j)r}\Bigr) =
\sum_{i\lt r} \sum_{l\lt m} v_l^{(i)} x^{lr+i},
$$

where $v_l^{(i)} = s_{lr+i} - \sum_{j\lt l} A_{m-1-j} s_{(l-1-j)r+i}$ are the decimation
coefficients. The second factor on the left is the denominator
$1 - A_{m-1} x^r - A_{m-2} x^{2r} - \cdots - A_0 x^{mr}$ of the generating function.

The printed denominator ends in $- A_1 x^{mr} - A_0$ and the printed hypothesis names
Relation (1); this is the reading of the paper's derivation and of its Example 2 ($m = 2$:
$1 - A_1 x^r - A_0 x^{2r}$).

## Sources

- Emre Güday and Murat Sahin, *Linear Recurrence Relations Satisfied by the General Conditional Sequences*, INTEGERS 26 (2026), Article A5, Theorem 1.
