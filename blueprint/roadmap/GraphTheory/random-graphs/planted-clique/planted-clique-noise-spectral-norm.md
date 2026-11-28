# Spectral norm of planted-clique noise is O(sqrt n)

There is an absolute constant $C$ such that for every $n \ge 1$, every planted set $S$ and every $t > 0$, the noise matrix $W$ of $G(n,1/2,S)$ satisfies

$$
\Pr\bigl[\|W\|_{2 \to 2} > C(\sqrt n + t)\bigr] \le 4e^{-t^2};
$$

in particular $\Pr\bigl[\|W\|_{2 \to 2} > 2C\sqrt n\bigr] \le 4e^{-n}$.

## Proof sketch

The entries of $W$ on and above the diagonal are independent, have mean zero and are bounded by $1$, hence sub-gaussian with a norm bounded by an absolute constant; the bound is the norm bound for symmetric random matrices with such entries.

Explicit constant: $\Pr[\|W\|_{2 \to 2} > 36\sqrt n] \le 2e^{-n}$. For fixed unit vectors $x, y$, $x^{\mathsf T} W y$ is a weighted sum of independent signs, so it exceeds $9\sqrt n$ with probability exponentially small in $n$. A $1/2$-net of the unit ball of size at most $5^n$ reduces the operator norm to at most $25^n$ such bilinear forms (losing a factor $4$), and a union bound gives $2 \cdot 25^n e^{-81n/4} \le 2e^{-n}$. Combined with the outside-degree lemma by a union bound, any recovery map that returns $S$ whenever $\|W\| \le 36\sqrt n$ and every outside vertex has at most $\tfrac58|S|$ neighbors in $S$ fails with probability at most $2e^{-n} + n e^{-|S|/32}$.

## Depends on

- [Planted clique model, search and detection problems](planted-clique-model.md)

## Proof depends on

- [Outside vertices have at most 5|S|/8 neighbors in the planted clique](planted-clique-outside-degrees.md)
- [Hoeffding's inequality for averages of bounded variables](../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- Noga Alon, Michael Krivelevich and Benny Sudakov, "Finding a large hidden clique in a random graph", Random Structures & Algorithms 13(3-4), 1998.
- R. Vershynin, "High-Dimensional Probability: An Introduction with Applications in Data Science", Cambridge University Press, 2018, Corollary 4.4.8 (with Theorem 4.4.5 and Example 2.5.8(c)).
