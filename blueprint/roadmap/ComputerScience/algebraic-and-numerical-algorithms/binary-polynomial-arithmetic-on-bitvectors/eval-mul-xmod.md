# Evaluation of modular multiplication by $X$

A width-$s$ binary word $w$ is a natural number $0 \le w < 2^s$, read through its binary digits $w = \sum_{i=0}^{s-1} w_i 2^i$ with $w_i \in \{0, 1\}$ (least significant bit first); the digit $w_i$ is taken to be $0$ for $i \ge s$. Its binary polynomial is $P_w = \sum_{i=0}^{s-1} w_i X^i \in \mathbb{F}_2[X]$ (the zero polynomial when $s = 0$).

For width-$s$ words $g$ and $w$, let $\mathrm{mulX}_g(w)$ be the width-$s$ word obtained by shifting $w$ left by one position inside width $s$ (the digit $w_{s-1}$ is dropped and the new lowest digit is $0$) and then, if $w_{s-1} = 1$, adding $g$ bitwise modulo $2$ (exclusive or); for $s = 0$ it is the empty word.

Let $R$ be a commutative ring, $\varphi \colon \mathbb{F}_2 \to R$ a ring homomorphism and $r \in R$, and write $\mathrm{ev}(p) = \sum_i \varphi(p_i) r^i$ for the evaluation at $r$ of $p = \sum_i p_i X^i \in \mathbb{F}_2[X]$. Let $g$ be a width-$s$ word such that

$$r^s = \mathrm{ev}(P_g).$$

Then for every width-$s$ word $w$,

$$\mathrm{ev}\bigl(P_{\mathrm{mulX}_g(w)}\bigr) = r \cdot \mathrm{ev}(P_w).$$

For $s = 0$ the hypothesis reads $1 = 0$, so it can only hold in the zero ring.
