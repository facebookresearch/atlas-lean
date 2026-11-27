# Spectral norm of planted-clique noise is O(sqrt n)

For every $n \ge 1$ and planted set $S$, the noise matrix $W$ of $G(n,1/2,S)$ satisfies

$$
\Pr\bigl[\|W\|_{2 \to 2} > 36\sqrt n\bigr] \le 2e^{-n}.
$$

Consequently any recovery map that returns $S$ whenever $\|W\| \le 36\sqrt n$ and every outside vertex has at most $\tfrac58|S|$ neighbors in $S$ fails with probability at most $2e^{-n} + n e^{-|S|/32}$.

## Proof sketch

For fixed unit vectors $x, y$, $x^{\mathsf T} W y$ is a weighted sum of independent signs, so it exceeds $9\sqrt n$ with probability exponentially small in $n$. A $1/2$-net of the unit ball of size at most $5^n$ reduces the operator norm to at most $25^n$ such bilinear forms (losing a factor $4$), and a union bound gives the tail. The recovery corollary is a union bound with the outside-degree lemma.

## Depends on

- [Planted clique model, search and detection problems](planted-clique-model.md)

## Proof depends on

- [Outside vertices have at most 5|S|/8 neighbors in the planted clique](planted-clique-outside-degrees.md)
- [Hoeffding's inequality for averages of bounded variables](../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- Noga Alon, Michael Krivelevich and Benny Sudakov, "Finding a large hidden clique in a random graph", Random Structures & Algorithms 13(3-4), 1998.
