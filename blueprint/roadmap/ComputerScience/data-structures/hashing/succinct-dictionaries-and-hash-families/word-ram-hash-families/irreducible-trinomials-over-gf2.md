# The trinomials x^(2·3^t) + x^(3^t) + 1 are irreducible over GF(2)

For every $t \ge 0$ the polynomial $x^{2 \cdot 3^t} + x^{3^t} + 1$ is irreducible over $\mathbb{F}_2$. Hence $\mathbb{F}_2[x] / (x^{2 \cdot 3^t} + x^{3^t} + 1)$ is a field with $2^{2 \cdot 3^t}$ elements, whose elements are bit strings of length $q = 2 \cdot 3^t$ with carry-less polynomial arithmetic. Choosing the least $t$ with $2 \cdot 3^t \ge q_0$ gives a field of $2^q$ elements with $q_0 \le q < 3 q_0$ for any required bit length $q_0 \ge 2$.

## Proof sketch

The polynomial is $\Phi_{3^{t+1}}(x)$, the cyclotomic polynomial of order $3^{t+1}$ over $\mathbb{F}_2$, since $\Phi_{3^{t+1}}(x) = \Phi_3(x^{3^t})$. For odd $n$, $\Phi_n$ factors over $\mathbb{F}_2$ into $\varphi(n)/d$ distinct irreducible factors of degree $d$, the multiplicative order of $2$ modulo $n$ (Lidl–Niederreiter, Theorem 2.47), so it is irreducible iff $2$ has order $\varphi(n)$ modulo $n$; and $2$ is a primitive root modulo every power of $3$ because it is a primitive root modulo $9$. Equivalently, for $t \ge 1$, Lidl–Niederreiter Theorem 3.35 applied to $f = x^2 + x + 1$ (irreducible of degree $2$ and order $3$ over $\mathbb{F}_2$) and $t' = 3^t$ shows that $f(x^{3^t})$ is irreducible of degree $2 \cdot 3^t$, since $3$ divides the order $3$ but not $(2^2 - 1)/3 = 1$ and $4 \nmid 3^t$.

## Sources

- R. Lidl and H. Niederreiter, "Finite Fields", 2nd edition, Cambridge University Press, 1997, Theorem 2.47 (factorization of cyclotomic polynomials over finite fields) and Theorem 3.35 (irreducibility of $f(x^t)$).
