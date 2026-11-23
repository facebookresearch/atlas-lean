# Modular powering matches the polynomial quotient

A width-$s$ binary word $w$ is a natural number $0 \le w < 2^s$, read through its binary digits $w = \sum_{i=0}^{s-1} w_i 2^i$ with $w_i \in \{0, 1\}$ (least significant bit first); the digit $w_i$ is taken to be $0$ for $i \ge s$. Its binary polynomial is $P_w = \sum_{i=0}^{s-1} w_i X^i \in \mathbb{F}_2[X]$ (the zero polynomial when $s = 0$).

For a width-$s$ word $g$, let $M_g = X^s + P_g$, a monic polynomial of degree $s$, let $Q_g = \mathbb{F}_2[X]/(M_g)$, write $[p]$ for the class of $p \in \mathbb{F}_2[X]$ in $Q_g$ and $\theta = [X]$. Let $\Phi_g$ be the bijection from width-$s$ words to $Q_g$ given by $\Phi_g(w) = [P_w]$.

For width-$s$ words $g$ and $w$, let $\mathrm{mulX}_g(w)$ be the width-$s$ word obtained by shifting $w$ left by one position inside width $s$ (the digit $w_{s-1}$ is dropped and the new lowest digit is $0$) and then, if $w_{s-1} = 1$, adding $g$ bitwise modulo $2$ (exclusive or); for $s = 0$ it is the empty word. For width-$s$ words $g$, $x$ and a width-$t$ word $y$, let $\mathrm{mulMod}_g(x, y)$ be the Horner value $c_0$ of the recursion $c_t = 0$, $c_j = \mathrm{mulX}_g(c_{j+1}) \oplus y_j x$ for $j = t-1, \dots, 0$, where $\oplus$ is bitwise exclusive or and $y_j x$ is $x$ if $y_j = 1$ and $0$ otherwise. Let $\mathrm{powMod}_g(u, e)$ be obtained from the width-$s$ word $1$ by applying $c \mapsto \mathrm{mulMod}_g(c, u)$ exactly $e$ times. Then for every width-$t$ word $u$ (any natural number $t$) and every natural number $e$,

$$\Phi_g\bigl(\mathrm{powMod}_g(u, e)\bigr) = [P_u]^e,$$

with $[P_u]^0 = 1$. No restriction on $s$ is needed: for $s = 0$ the ring $Q_g$ is the zero ring and both sides agree trivially.
