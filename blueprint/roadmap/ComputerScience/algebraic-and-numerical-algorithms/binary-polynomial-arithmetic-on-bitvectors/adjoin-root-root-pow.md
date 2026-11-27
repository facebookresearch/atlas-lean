# Reduction of the root power in a binary residue ring

A width-$s$ binary word $w$ is a natural number $0 \le w < 2^s$, read through its binary digits $w = \sum_{i=0}^{s-1} w_i 2^i$ with $w_i \in \{0, 1\}$ (least significant bit first); the digit $w_i$ is taken to be $0$ for $i \ge s$. Its binary polynomial is $P_w = \sum_{i=0}^{s-1} w_i X^i \in \mathbb{F}_2[X]$ (the zero polynomial when $s = 0$).

For a width-$s$ word $g$, let $M_g = X^s + P_g$, a monic polynomial of degree $s$, let $Q_g = \mathbb{F}_2[X]/(M_g)$, write $[p]$ for the class of $p \in \mathbb{F}_2[X]$ in $Q_g$ and $\theta = [X]$. Let $\Phi_g$ be the bijection from width-$s$ words to $Q_g$ given by $\Phi_g(w) = [P_w]$. Then

$$\theta^s = \Phi_g(g) = [P_g] \quad \text{in } Q_g,$$

which is the defining relation $\theta^s + [P_g] = 0$ rewritten using characteristic $2$.
