# Forward map of the binary word residue equivalence

A width-$s$ binary word $w$ is a natural number $0 \le w < 2^s$, read through its binary digits $w = \sum_{i=0}^{s-1} w_i 2^i$ with $w_i \in \{0, 1\}$ (least significant bit first); the digit $w_i$ is taken to be $0$ for $i \ge s$. Its binary polynomial is $P_w = \sum_{i=0}^{s-1} w_i X^i \in \mathbb{F}_2[X]$ (the zero polynomial when $s = 0$).

For a width-$s$ word $g$, let $M_g = X^s + P_g$, a monic polynomial of degree $s$, let $Q_g = \mathbb{F}_2[X]/(M_g)$, write $[p]$ for the class of $p \in \mathbb{F}_2[X]$ in $Q_g$ and $\theta = [X]$. For width-$s$ words $g$ and $w$, the bijection $\Phi_g$ from width-$s$ words onto $Q_g$ satisfies

$$\Phi_g(w) = [P_w],$$

the class of the binary polynomial of $w$ modulo $M_g$.
