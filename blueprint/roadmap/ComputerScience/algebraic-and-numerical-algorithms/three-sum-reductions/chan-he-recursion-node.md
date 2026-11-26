# One node of the Chan-He recursion

At a node with finite sets of integers $P, Q, R$ and a modulus $M \ge 1$, call an element **light** if no other element of its own set is congruent to it modulo $M$, and **heavy** otherwise. Let $K > 3\max\{|a| : a \in P \cup Q \cup R\}$ with $K \ge 1$, and form arrays $X, Y, Z$ of length $2M$: $X[i] = p$ when $i < M$ and $p$ is the light element of $P$ with $p \bmod M = i$, $Y[j] = q$ likewise for $Q$, and $Z[\rho] = Z[\rho + M] = -r$ when $r$ is the light element of $R$ with $(-r) \bmod M = \rho$; every other entry of $X$ and $Y$ is $K$ and every other entry of $Z$ is $4K$. Then $(P, Q, R)$ has a solution with all three elements light if and only if the Convolution-3SUM instance $(X, Y, Z)$ with $N = 2M$ has a solution. Every solution of $(P, Q, R)$ that uses a heavy element of $P$ (respectively $Q$, $R$) is a solution of the child node in which $P$ (respectively $Q$, $R$) is replaced by its set of heavy elements.

## Proof sketch

If $p + q + r = 0$ with all three light, then $i = p \bmod M$ and $j = q \bmod M$ satisfy $i + j < 2M$ and $i + j \equiv -r \pmod M$, so $i + j \in \{\rho, \rho + M\}$ and $X[i] + Y[j] = Z[i + j]$. Conversely, a sum involving a filler entry $K$ or $4K$ cannot match, since all real entries have absolute value below $K/3$; so a solution reads $p + q = -r$ for light $p, q, r$.

## Depends on

- [Convolution-3SUM](convolution-three-sum.md)
- [Choosing a hashing modulus with few heavy elements](chan-he-modulus-choice.md)

## Sources

- T. M. Chan and Q. He, "Reducing 3SUM to Convolution-3SUM", Symposium on Simplicity in Algorithms (SOSA), 2020.
