# The trinomials x^(2·3^t) + x^(3^t) + 1 are irreducible over GF(2)

For every $t \ge 0$ the polynomial $x^{2 \cdot 3^t} + x^{3^t} + 1$ is irreducible over $\mathbb{F}_2$. Hence $\mathbb{F}_2[x] / (x^{2 \cdot 3^t} + x^{3^t} + 1)$ is a field with $2^{2 \cdot 3^t}$ elements, whose elements are bit strings of length $q = 2 \cdot 3^t$ with carry-less polynomial arithmetic. Choosing the least $t$ with $2 \cdot 3^t \ge q_0$ gives a field of $2^q$ elements with $q_0 \le q < 3 q_0$ for any required bit length $q_0 \ge 2$.

## Proof sketch

The polynomial is $\Phi_{3^{t+1}}(x)$, the cyclotomic polynomial of order $3^{t+1}$ over $\mathbb{F}_2$, since $\Phi_{3^{t+1}}(x) = \Phi_3(x^{3^t})$. A cyclotomic polynomial $\Phi_n$ is irreducible over $\mathbb{F}_2$ iff $2$ has multiplicative order $\varphi(n)$ modulo $n$, and $2$ is a primitive root modulo every power of $3$ because it is a primitive root modulo $9$.

## Sources

- R. Lidl and H. Niederreiter, "Finite Fields", 2nd edition, Cambridge University Press, 1997.
- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science 7(1-3), 2012.
