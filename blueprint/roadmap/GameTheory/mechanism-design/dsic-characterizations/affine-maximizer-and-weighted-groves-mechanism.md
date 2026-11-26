# Affine maximizer and weighted Groves mechanism

A social choice rule $f$ is an *affine maximizer* on a subrange $A \subseteq \Omega$ if there are nonnegative agent weights $w_i$, not all zero, and outcome constants $c : A \to \mathbb{R}$ such that $f(b) \in \arg\max_{a \in A}\, \bigl(c(a) + \sum_i w_i b_i(a)\bigr)$ for every report profile $b$. The *weighted Groves mechanism* with positive weights charges agent $i$ the payment $h_i(b_{-i}) - \frac1{w_i}\bigl(c(f(b)) + \sum_{j \ne i} w_j b_j(f(b))\bigr)$.

## Depends on

- [Groves payment](../vickrey-clarke-groves-mechanisms/groves-payment.md)
- [Social welfare](../vickrey-clarke-groves-mechanisms/welfare.md)

## Sources

- Noam Nisan, "Introduction to Mechanism Design (for Computer Scientists)", Algorithmic Game Theory, Cambridge University Press, 2007.
- Ron Lavi, "Computationally Efficient Approximation Mechanisms", Algorithmic Game Theory, Cambridge University Press, 2007.
