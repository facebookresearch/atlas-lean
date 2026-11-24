# Modular multiplication of binary polynomial residues

A width-$s$ binary word $w$ is a natural number $0 \le w < 2^s$, read through its binary digits $w = \sum_{i=0}^{s-1} w_i 2^i$ with $w_i \in \{0, 1\}$ (least significant bit first); the digit $w_i$ is taken to be $0$ for $i \ge s$. For width-$s$ words $g$, $c$, let $\mathrm{mulX}_g(c)$ be $c$ shifted left by one position within width $s$, followed by a bitwise exclusive or with $g$ when the digit $c_{s-1}$ shifted out is $1$. For width-$s$ words $g$, $x$ and a width-$t$ word $y$ (with $t$ arbitrary), $\mathrm{mulMod}_g(x, y)$ is the width-$s$ word $c_0$ computed by Horner's rule on the digits of $y$, from the most significant down:

$$c_t = 0, \qquad c_j = \begin{cases} x \oplus \mathrm{mulX}_g(c_{j+1}) & \text{if } y_j = 1, \\ \mathrm{mulX}_g(c_{j+1}) & \text{if } y_j = 0, \end{cases} \qquad j = t-1, \dots, 0,$$

where $\oplus$ is bitwise exclusive or. For $t = 0$ the result is the zero word.

In terms of binary polynomials, the result represents $P_x P_y$ modulo $X^s + P_g$.
