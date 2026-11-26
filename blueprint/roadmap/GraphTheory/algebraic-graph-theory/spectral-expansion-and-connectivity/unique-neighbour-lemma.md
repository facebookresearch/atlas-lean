# Unique-neighbour lemma for bipartite vertex expanders

Let $G$ be a bipartite graph between finite sets $L$ and $R$ in which every left vertex has at most $c$ neighbours. For $S \subseteq L$ let $N(S)$ be its neighbourhood and $U(S)$ the set of right vertices with exactly one neighbour in $S$. Then $2|N(S)| \le |U(S)| + c|S|$. Hence if $G$ is a vertex expander with factor $\alpha$ for sets of size at most $k$ (every $S$ with $|S| \le k$ has $|N(S)| \ge \alpha|S|$), then every such $S$ has

$$|U(S)| \ge (2\alpha - c)\,|S|;$$

for a lossless expander, $\alpha = c(1 - \varepsilon)$, this is $|U(S)| \ge c(1 - 2\varepsilon)|S|$.

## Proof sketch

Count the at most $c|S|$ edges leaving $S$: each unique neighbour absorbs one edge and every other neighbour absorbs at least two, so $|U(S)| + 2(|N(S)| - |U(S)|) \le c|S|$. Substitute the expansion bound.

## Sources

- V. Guruswami, A. Rudra, M. Sudan, "Essential Coding Theory", draft book, 2019.
- M. Sipser, D. A. Spielman, "Expander Codes", IEEE Transactions on Information Theory, 1996.
