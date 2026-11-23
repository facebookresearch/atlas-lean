# Generating function for the adjusted $(2,1)$-hook tableau counts

Let $k$ be a natural
number, and let $\mathrm{SYT}_k(2,1;n)$ be the number of standard Young tableaux with $n$ cells
in the $(2,1)$-hook whose first two rows differ in length by $k$. Set
$T_{n,k} = \mathrm{SYT}_k(2,1;n) + (-1)^{n+k+1}$ for $n \ge k$ and $T_{n,k} = 0$ for $n < k$, and
let $M(x) = \sum_{n \ge 0} m_n x^n$ be the generating function of the Motzkin numbers $m_n$.
Then in the ring $\mathbb{Z}[[x]]$ of formal power series

$$(1 + x) \sum_{n \ge 0} T_{n,k} x^n = (x M(x))^{k+1}.$$

Equivalently, $\sum_{n \ge k} T_{n,k} x^n = x^{k+1} M(x)^{k+1} / (1 + x)$; the identity is
stated without division.

## Sources

- Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal of Integer Sequences 28 (2025), Article 25.8.1, Lemma 7 (`jis-2025-25.8.1-lem-7`).
