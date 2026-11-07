# Remainder form of the weighted power-sum equation for Lucas sequences

Let $x$ be a
positive integer, let $y \in \{1, -1\}$, and let $(U_n)$ be the Lucas sequence with parameters
$(x, y)$, given by $U_0 = 0$, $U_1 = 1$ and $U_{n+2} = x U_{n+1} - y U_n$. Suppose
$D = x^2 - 4y > 0$ and put $\alpha = (x + \sqrt{D})/2$. Let $n, p, q$ be positive integers and
$k \geq 3$ an integer with

$$
\sum_{j=1}^{k} j \, U_j^p = U_n^q.
$$

Then there are real numbers $R_1, R_2$ with $|R_1| < k^2 \alpha^{k(p-2)}$,
$|R_2| < \alpha^{n(q-2)}$ and

$$
\frac{D^{(q-p)/2} (k\alpha^p - (k+1))}{(\alpha^p - 1)^2} \alpha^{p(k+1)} - \alpha^{qn} =
D^{q/2} R_2 - D^{q/2} R_1 - \frac{D^{(q-p)/2} \alpha^p}{(\alpha^p - 1)^2}.
$$

The remainders $R_1, R_2$ are only asserted to exist; the source defines them explicitly in its
proof.

## Sources

- Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024), no. 3, Proposition 4.1 (`fq-2024-earplynch07182024-prop-4.1`).
