# Evaluation of modular powering

A width-$s$ binary word $w$ is a natural number $0 \le w < 2^s$, read through its binary digits $w = \sum_{i=0}^{s-1} w_i 2^i$ with $w_i \in \{0, 1\}$ (least significant bit first); the digit $w_i$ is taken to be $0$ for $i \ge s$. Its binary polynomial is $P_w = \sum_{i=0}^{s-1} w_i X^i \in \mathbb{F}_2[X]$ (the zero polynomial when $s = 0$).

For width-$s$ words $g$ and $w$, let $\mathrm{mulX}_g(w)$ be the width-$s$ word obtained by shifting $w$ left by one position inside width $s$ (the digit $w_{s-1}$ is dropped and the new lowest digit is $0$) and then, if $w_{s-1} = 1$, adding $g$ bitwise modulo $2$ (exclusive or); for $s = 0$ it is the empty word. For width-$s$ words $g$, $x$ and a width-$t$ word $y$, let $\mathrm{mulMod}_g(x, y)$ be the Horner value $c_0$ of the recursion $c_t = 0$, $c_j = \mathrm{mulX}_g(c_{j+1}) \oplus y_j x$ for $j = t-1, \dots, 0$, where $\oplus$ is bitwise exclusive or and $y_j x$ is $x$ if $y_j = 1$ and $0$ otherwise. Let $\mathrm{powMod}_g(u, e)$ be obtained from the width-$s$ word $1$ by applying $c \mapsto \mathrm{mulMod}_g(c, u)$ exactly $e$ times.

Let $R$ be a commutative ring, $\varphi \colon \mathbb{F}_2 \to R$ a ring homomorphism and $r \in R$, and write $\mathrm{ev}(p) = \sum_i \varphi(p_i) r^i$ for the evaluation at $r$ of $p = \sum_i p_i X^i \in \mathbb{F}_2[X]$. Assume $s \ge 1$ and let $g$ be a width-$s$ word such that

$$r^s = \mathrm{ev}(P_g).$$

Then for every width-$t$ word $u$ (any natural number $t$) and every natural number $e$,

$$\mathrm{ev}\bigl(P_{\mathrm{powMod}_g(u, e)}\bigr) = \mathrm{ev}(P_u)^e,$$

with $\mathrm{ev}(P_u)^0 = 1$. The hypothesis $s \ge 1$ ensures that the starting word $1$ encodes the polynomial $1$.
