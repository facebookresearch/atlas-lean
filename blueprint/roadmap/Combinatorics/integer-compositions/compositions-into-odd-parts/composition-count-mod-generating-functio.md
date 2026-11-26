# Bowman's generating function for compositions with a part count in a residue class

Let $A \subseteq \mathbb{N}$ and let $j_A(x) = \sum_{a \in A,\, a \ge 1} x^a \in \mathbb{Q}[[x]]$. Let $b_A(m, q; n)$ be the number of compositions of $n$ with all parts in $A$ and a number of parts congruent to $q$ modulo $m$. For all natural numbers $m$ and $q$ with $q < m$, in $\mathbb{Q}[[x]]$,

$$\sum_{n \ge 0} b_A(m, q; n)\, x^n = \frac{j_A(x)^q}{1 - j_A(x)^m}.$$

The hypothesis $q < m$ forces $m \ge 1$, so $1 - j_A(x)^m$ has constant term $1$ and is invertible.

## Sources

- Joshua P. Bowman, *Compositions with an Odd Number of Parts, and Other Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6, Theorem 3.
