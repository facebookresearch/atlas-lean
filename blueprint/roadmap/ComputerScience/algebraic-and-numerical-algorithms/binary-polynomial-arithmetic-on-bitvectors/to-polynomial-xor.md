# Bitwise xor corresponds to polynomial addition over $\mathbb{F}_2$

A width-$s$ binary word $w$ is a natural number $0 \le w < 2^s$, read through its binary digits $w = \sum_{i=0}^{s-1} w_i 2^i$ with $w_i \in \{0, 1\}$ (least significant bit first); the digit $w_i$ is taken to be $0$ for $i \ge s$. Its binary polynomial is $P_w = \sum_{i=0}^{s-1} w_i X^i \in \mathbb{F}_2[X]$ (the zero polynomial when $s = 0$). For width-$s$ words $x$ and $y$, let $x \oplus y$ be their bitwise exclusive or, with digits $(x \oplus y)_i = x_i + y_i \bmod 2$. Then

$$P_{x \oplus y} = P_x + P_y \quad \text{in } \mathbb{F}_2[X].$$

The corresponding statement fails for integer addition modulo $2^s$, which propagates carries.
