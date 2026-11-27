# Monic binary modulus of a fixed-width word

A width-$s$ binary word $w$ is a natural number $0 \le w < 2^s$, read through its binary digits $w = \sum_{i=0}^{s-1} w_i 2^i$ with $w_i \in \{0, 1\}$ (least significant bit first); the digit $w_i$ is taken to be $0$ for $i \ge s$. Its binary polynomial is $P_w = \sum_{i=0}^{s-1} w_i X^i \in \mathbb{F}_2[X]$ (the zero polynomial when $s = 0$). The binary modulus of a width-$s$ word $g$ is

$$M_g = X^s + P_g \in \mathbb{F}_2[X],$$

so $g$ lists the coefficients of $X^0, \dots, X^{s-1}$ below the leading term $X^s$. For $s = 0$, $M_g = 1$.
