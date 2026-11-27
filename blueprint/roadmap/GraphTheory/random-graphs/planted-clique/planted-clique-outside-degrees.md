# Outside vertices have at most 5|S|/8 neighbors in the planted clique

In $G(n, 1/2, S)$ with $|S| \ge 1$, the probability that some vertex $v \notin S$ has more than $\tfrac58 |S|$ neighbors in $S$ is at most $n\,e^{-|S|/32}$.

## Proof sketch

For fixed $v \notin S$, its $|S|$ edges into $S$ are independent fair coins, so Hoeffding's inequality bounds the probability of more than $|S|/2 + |S|/8$ neighbors by $e^{-2(|S|/8)^2/|S|} = e^{-|S|/32}$. A union bound over at most $n$ vertices finishes.

## Depends on

- [Planted clique model, search and detection problems](planted-clique-model.md)

## Proof depends on

- [Hoeffding's inequality for averages of bounded variables](../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- Noga Alon, Michael Krivelevich and Benny Sudakov, "Finding a large hidden clique in a random graph", Random Structures & Algorithms 13(3-4), 1998.
