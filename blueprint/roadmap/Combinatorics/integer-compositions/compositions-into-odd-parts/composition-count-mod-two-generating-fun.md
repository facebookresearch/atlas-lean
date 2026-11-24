# Generating functions for compositions with an even or odd number of parts

Let $A \subseteq \mathbb{N}$ and let $j_A(x) = \sum_{a \in A,\, a \ge 1} x^a \in \mathbb{Q}[[x]]$ and let $j_A'(x)$ be its formal derivative. Let $b_A(2, q; n)$ and $c_A(2, q; n)$ be the numbers of compositions and of circular compositions of $n$ with all parts in $A$ and a number of parts congruent to $q$ modulo $2$. For $q \in \{0, 1\}$, in $\mathbb{Q}[[x]]$,

$$\sum_{n \ge 0} b_A(2, q; n)\, x^n = \frac{1}{2} \cdot \frac{1}{1 - j_A(x)} + \frac{1}{2} \cdot \frac{(-1)^q}{1 + j_A(x)}$$

and

$$\sum_{n \ge 0} c_A(2, q; n)\, x^n = \frac{1}{2} \cdot \frac{x\, j_A'(x)}{1 - j_A(x)} + \frac{1}{2} \cdot \frac{(-1)^{q+1}\, x\, j_A'(x)}{1 + j_A(x)}.$$

## Sources

- Joshua P. Bowman, *Compositions with an Odd Number of Parts, and Other Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6, Corollary 6.
