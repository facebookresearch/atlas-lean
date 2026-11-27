# Bitvector of the low coefficients of a binary polynomial

A width-$s$ binary word $w$ is a natural number $0 \le w < 2^s$, read through its binary digits $w = \sum_{i=0}^{s-1} w_i 2^i$ with $w_i \in \{0, 1\}$ (least significant bit first); the digit $w_i$ is taken to be $0$ for $i \ge s$. For a natural number $s$ and a polynomial $p = \sum_i p_i X^i \in \mathbb{F}_2[X]$, $\mathrm{trunc}_s(p)$ is the width-$s$ word whose digit $i$ is $p_i$ for $0 \le i < s$, that is, $\mathrm{trunc}_s(p) = \sum_{i=0}^{s-1} p_i 2^i$ with $p_i \in \{0, 1\}$.

Coefficients of index at least $s$ are discarded, so $\mathrm{trunc}_s(p)$ depends only on $p$ modulo $X^s$; for $s = 0$ the result is the empty word.
