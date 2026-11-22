# Bitvector encoding recovers the original word

A width-$s$ binary word $w$ is a natural number $0 \le w < 2^s$, read through its binary digits $w = \sum_{i=0}^{s-1} w_i 2^i$ with $w_i \in \{0, 1\}$ (least significant bit first); the digit $w_i$ is taken to be $0$ for $i \ge s$. Its binary polynomial is $P_w = \sum_{i=0}^{s-1} w_i X^i \in \mathbb{F}_2[X]$ (the zero polynomial when $s = 0$). For $p \in \mathbb{F}_2[X]$, let $\mathrm{trunc}_s(p)$ be the width-$s$ word whose digit $i$ is the coefficient of $X^i$ in $p$ for $i < s$. Then for every width-$s$ word $w$,

$$\mathrm{trunc}_s(P_w) = w.$$
