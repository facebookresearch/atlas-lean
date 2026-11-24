# Multiplication by $X$ of a binary polynomial residue

A width-$s$ binary word $w$ is a natural number $0 \le w < 2^s$, read through its binary digits $w = \sum_{i=0}^{s-1} w_i 2^i$ with $w_i \in \{0, 1\}$ (least significant bit first); the digit $w_i$ is taken to be $0$ for $i \ge s$. For width-$s$ words $g$ and $w$, let $w \ll 1$ be $w$ shifted left by one position within width $s$, that is $2w \bmod 2^s$ (digit $w_{s-1}$ is dropped and the new digit $0$ is $0$). The word $\mathrm{mulX}_g(w)$ is

$$\mathrm{mulX}_g(w) = \begin{cases} (w \ll 1) \oplus g & \text{if } s \ge 1 \text{ and } w_{s-1} = 1, \\ w \ll 1 & \text{otherwise,} \end{cases}$$

where $\oplus$ is bitwise exclusive or. For $s = 0$ the result is the empty word.

In terms of binary polynomials $P_w = \sum_{i<s} w_i X^i$, the result encodes $X P_w + w_{s-1}(X^s + P_g)$, that is, $X P_w$ reduced once by the modulus $X^s + P_g$ when its degree reaches $s$.
