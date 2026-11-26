# Generating function for humps of a fixed height

Let $H_{n,k}$ be the number of pairs
$(P, h)$ where $P$ is a Motzkin path of length $n$ and $h$ is a hump of height $k$ in $P$ (an up
step and a later down step with only flat steps between them, the up step ending at height
$k$), and let $M(x) = \sum_{n \ge 0} m_n x^n$, where $m_n$ is the $n$-th Motzkin number. For
every integer $k \ge 1$, in the ring $\mathbb{Z}[[x]]$ of formal power series,

$$(1 - x) \sum_{n \ge 2k} H_{n,k} \, x^n = x^{2k} M(x)^{2k}.$$

The source also states this result in Riordan-array form.

## Sources

- Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal of Integer Sequences 28 (2025), Article 25.8.1, Corollary 5 (`jis-2025-25.8.1-cor-5`).
