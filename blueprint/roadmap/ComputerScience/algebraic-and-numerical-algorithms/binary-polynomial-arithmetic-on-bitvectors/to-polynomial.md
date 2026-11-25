# Binary polynomial of a bitvector

A width-$s$ binary word $w$ is a natural number $0 \le w < 2^s$, read through its binary digits $w = \sum_{i=0}^{s-1} w_i 2^i$ with $w_i \in \{0, 1\}$ (least significant bit first); the digit $w_i$ is taken to be $0$ for $i \ge s$. The binary polynomial of $w$ is

$$P_w = \sum_{i=0}^{s-1} w_i X^i \in \mathbb{F}_2[X],$$

whose coefficient of $X^i$ is the $i$-th least significant digit of $w$. For $s = 0$ it is the zero polynomial.
