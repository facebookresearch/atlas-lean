# Cyclic compositions with an even or odd number of parts

Let $A \subseteq \mathbb{N}$ and let $j_A(x) = \sum_{a \in A,\, a \ge 1} x^a \in \mathbb{Q}[[x]]$ and $L_{2,s}(y) = \sum_{r \ge 1,\ r \equiv s \pmod 2} y^r / r \in \mathbb{Q}[[y]]$. Let $d_A(2, q; n)$ be the number of cyclic compositions of $n$ with all parts in $A$ and a number of parts congruent to $q$ modulo $2$, and let $\varphi$ be Euler's totient function. For every natural number $n$, in $\mathbb{Q}$, with $k$ running over positive divisors of $n$,

$$d_A(2, 0; n) = \frac{1}{2} \sum_{k \mid n} \frac{\varphi(k)}{k} \cdot 2\, [x^{n/k}]\, L_{2,0}\bigl(j_A(x)\bigr) + \frac{1}{2} \sum_{\substack{k \mid n \\ k \text{ even}}} \frac{\varphi(k)}{k} \cdot 2\, [x^{n/k}]\, L_{2,1}\bigl(j_A(x)\bigr)$$

and

$$d_A(2, 1; n) = \frac{1}{2} \sum_{\substack{k \mid n \\ k \text{ odd}}} \frac{\varphi(k)}{k} \cdot 2\, [x^{n/k}]\, L_{2,1}\bigl(j_A(x)\bigr).$$

Since $2 L_{2,0}(y) = \log \frac{1}{1 - y^2}$ and $2 L_{2,1}(y) = \log \frac{1 + y}{1 - y}$, these are the coefficients of Bowman's logarithmic generating functions for cyclic compositions with an even and with an odd number of parts. For $n = 0$ all sums are empty and both counts are $0$.

## Sources

- Joshua P. Bowman, *Compositions with an Odd Number of Parts, and Other Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6, Corollary 6.
