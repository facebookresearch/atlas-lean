# Binary Krawtchouk polynomials

For $0 \le k \le n$, the *binary Krawtchouk polynomial* of degree $k$ is

$$
K_k(x) = \sum_{j=0}^{k} (-1)^{j} \binom{x}{j}\binom{n - x}{k - j}.
$$

For $x \in \{0,1\}^n$ of Hamming weight $i$, $K_k(i) = \sum_{y : |y| = k} (-1)^{x \cdot y}$, so $K_k$ evaluated at weights gives the eigenvalues of the distance-$k$ graph of the hypercube on the characters.

## Sources

- Philippe Delsarte, "An algebraic approach to the association schemes of coding theory", Philips Research Reports Supplements 10 (1973).
- F. J. MacWilliams, N. J. A. Sloane, "The Theory of Error-Correcting Codes", North-Holland (1977).
