# Closed form for the Jacobsthal numbers

Let $J : \mathbb{N} \to \mathbb{N}$ satisfy $J(0) = J(1) = 1$ and
$J(n+2) = J(n+1) + 2J(n)$ for every $n \in \mathbb{N}$. Then for every $m \in \mathbb{N}$,

$$J(m) = \frac{2^{m+1} + (-1)^m}{3}.$$

The source cites A. Tucker, "Applied Combinatorics," 3rd edition, for this formula. The proof
applies Binet's formula for second-order linear recurrences; the characteristic polynomial
$x^2 - x - 2$ has roots $2$ and $-1$.

## Sources

- Darrin D. Frey and James A. Sellers, "Jacobsthal Numbers and Alternating Sign Matrices," Journal of Integer Sequences 3 (2000), Article 00.2.3, recurrence (2) with initial values $J_0 = J_1 = 1$, and Theorem 2.2, equation (5), <https://cs.uwaterloo.ca/journals/JIS/VOL3/SELLERS/sellers.html>
