# Modular powering of binary polynomial residues

A width-$s$ binary word $w$ is a natural number $0 \le w < 2^s$, read through its binary digits $w = \sum_{i=0}^{s-1} w_i 2^i$ with $w_i \in \{0, 1\}$ (least significant bit first); the digit $w_i$ is taken to be $0$ for $i \ge s$. For width-$s$ words $g$, $c$ and a width-$t$ word $u$, let $\mathrm{mulMod}_g(c, u)$ be the Horner modular product of $c$ by $u$ (the width-$s$ word representing $P_c P_u$ modulo $X^s + P_g$). For a natural number $e$, $\mathrm{powMod}_g(u, e)$ is the width-$s$ word

$$c_0 = 1, \qquad c_{k+1} = \mathrm{mulMod}_g(c_k, u), \qquad \mathrm{powMod}_g(u, e) = c_e,$$

so $e$ successive multiplications by $u$ starting from the word $1$; for $e = 0$ the result is the word $1$, which for $s = 0$ is the empty word.
