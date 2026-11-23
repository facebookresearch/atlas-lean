# Cyclic sum formula (Hoffman–Ohno)

For a finite list $(n_1, \dots, n_r)$ of natural numbers
let $\zeta(n_1, \dots, n_r)$ be the sum of $(m_1^{n_1} \cdots m_r^{n_r})^{-1}$ over all integers
$m_1 > m_2 > \cdots > m_r > 0$, taken to be $0$ when this family is not summable. Let
$k = (k_1, \dots, k_l)$ be a nonempty list of positive integers, not all equal to $1$, with
subscripts read modulo $l$. Then

$$
\sum_{j=1}^{l} \sum_{i=1}^{k_j - 1} \zeta(k_j - i + 1, k_{j+1}, \dots, k_{j+l-1}, i)
= \sum_{j=1}^{l} \zeta(k_j + 1, k_{j+1}, \dots, k_{j+l-1}),
$$

where the inner sum is empty when $k_j = 1$ and the run $k_{j+1}, \dots, k_{j+l-1}$ is empty
when $l = 1$.

## Sources

- Shingo Saito, Tatsushi Tanaka, and Noriko Wakabayashi, "Combinatorial Remarks on the Cyclic Sum Formula for Multiple Zeta Values," Journal of Integer Sequences 14 (2011), Article 11.2.4, Theorem `thm:CSF` ("Cyclic sum formula," first proved by Hoffman-Ohno), lines 242–248; index set `check{I}^1` at lines 150–166, <https://cs.uwaterloo.ca/journals/JIS/VOL14/Saito/saito22.tex>.
