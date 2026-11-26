# Bowman's generating function for circular compositions with a part count in a residue class

Let $A \subseteq \mathbb{N}$ and let $j_A(x) = \sum_{a \in A,\, a \ge 1} x^a \in \mathbb{Q}[[x]]$ and let $j_A'(x)$ be its formal derivative. Let $c_A(m, q; n)$ be the number of circular compositions of $n$ (nonempty sets of removed edges of the cycle $C_n$) with all parts in $A$ and a number of parts congruent to $q$ modulo $m$. For all natural numbers $m$ and $q$ with $q < m$, in $\mathbb{Q}[[x]]$,

$$\sum_{n \ge 0} c_A(m, q; n)\, x^n = \frac{x\, j_A(x)^e\, j_A'(x)}{1 - j_A(x)^m}, \qquad e = \begin{cases} m - 1 & \text{if } q = 0, \\ q - 1 & \text{if } q \ne 0. \end{cases}$$

## Sources

- Joshua P. Bowman, *Compositions with an Odd Number of Parts, and Other Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6, Theorem 3.
