# Closed form for Gutkovskiy's sequence

Let $g_0, g_1, \dots$ be Gutkovskiy's sequence,
let $|K_i|$ be the length of the Kimberling block $K_i$, and let $\alpha = (\sqrt{3} - 1)/2$ and
$\beta = \sqrt{3}/3$. Let $n$ be a natural number and let $a_0, a_1, \dots, a_{m-1}$ be digits in
$\{0, 1, 2\}$ such that no two consecutive digits $a_i, a_{i+1}$ are both $2$ and
$n = \sum_{i < m} a_i |K_i|$. If $m \ge 1$ and $a_0 = 1$, then
$g_n = 2\lfloor \alpha n \rfloor + 1$; if $m \ge 1$ and $a_0 \in \{0, 2\}$, then
$g_n = 2\lfloor \alpha n + \beta \rfloor$.

Written most significant digit first, $a_{m-1} \cdots a_1 a_0$ is a $K$-representation of $n$
ending in the digit $a_0$; leading zeros are allowed.

## Sources

- Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24 (2024), Article A51, Theorem 2 (`integers-2024-A51-thm-2`).
