# Concentration of the common neighborhood of a planted seed

In $G(n, 1/2, S)$ with $|S| < n$, let $T \subseteq S$ and let $N(T)$ be the common neighborhood of $T$ (vertices outside $T$ adjacent to all of $T$). Then $|N(T)| = |S| - |T| + Z$, where $Z$ is a sum of $n - |S|$ independent indicators, each of mean $2^{-|T|}$. Hence for every $\varepsilon \ge 0$,

$$
\Pr\Bigl[|N(T)| \ge |S| - |T| + \frac{n - |S|}{2^{|T|}} + \varepsilon\Bigr] \le \exp\Bigl(-\frac{2\varepsilon^2}{n - |S|}\Bigr),
$$

and $|N(T)| < |S| + 2n/2^{|T|}$ except with probability at most $\exp(-2n/4^{|T|})$. Moreover the edges not touching $T$ are independent of $N(T)$, so the graph induced on $N(T)$ is a fresh planted-clique instance with planted set $S \setminus T$.

## Proof sketch

Every vertex of $S \setminus T$ survives, and an outside vertex survives exactly when its $|T|$ edges into $T$ are all present; these edge blocks are disjoint across vertices, so the indicators are independent. Hoeffding's inequality gives both tails. The exposure coupling resamples only edges not touching $T$, which leaves $N(T)$ unchanged.

## Depends on

- [Planted clique model, search and detection problems](planted-clique-model.md)

## Proof depends on

- [Hoeffding's inequality for averages of bounded variables](../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- Noga Alon, Michael Krivelevich and Benny Sudakov, "Finding a large hidden clique in a random graph", Random Structures & Algorithms 13(3-4), 1998.
