# Fixed-width binary words as residues modulo a monic polynomial

A width-$s$ binary word $w$ is a natural number $0 \le w < 2^s$, read through its binary digits $w = \sum_{i=0}^{s-1} w_i 2^i$ with $w_i \in \{0, 1\}$ (least significant bit first); the digit $w_i$ is taken to be $0$ for $i \ge s$. Its binary polynomial is $P_w = \sum_{i=0}^{s-1} w_i X^i \in \mathbb{F}_2[X]$ (the zero polynomial when $s = 0$).

For a width-$s$ word $g$, let $M_g = X^s + P_g$, a monic polynomial of degree $s$, let $Q_g = \mathbb{F}_2[X]/(M_g)$, write $[p]$ for the class of $p \in \mathbb{F}_2[X]$ in $Q_g$ and $\theta = [X]$. Then the map

$$\Phi_g \colon w \mapsto [P_w]$$

is a bijection from the set of width-$s$ words onto $Q_g$. Its inverse sends a class $z$ to $\mathrm{trunc}_s(\rho(z))$, where $\rho(z)$ is the remainder of the division of any representative of $z$ by $M_g$ (a polynomial of degree less than $s$) and $\mathrm{trunc}_s$ reads off the coefficients of $X^0, \dots, X^{s-1}$ as digits.

The bijection is a bijection of sets only: it carries bitwise exclusive or to addition in $Q_g$, but not integer addition of words. For $s = 0$ both sides have exactly one element, $Q_g$ being the zero ring.
