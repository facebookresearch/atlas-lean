# Unique-neighbour lemma for bipartite vertex expanders

Let $G$ be a $c$-left-regular bipartite graph between finite sets $L$ and $R$ with $|L| = n$, and let $\gamma \ge 0$ and $\varepsilon < 1/2$. Suppose $G$ is a lossless expander: every $S \subseteq L$ with $|S| \le \gamma n$ has $|N(S)| \ge c(1 - \varepsilon)|S|$, where $N(S)$ is its neighbourhood. For $S \subseteq L$ let $U(S)$ be the set of right vertices with exactly one neighbour in $S$. Then every $S \subseteq L$ with $|S| \le \gamma n$ has

$$|U(S)| \ge c(1 - 2\varepsilon)\,|S|.$$

## Proof sketch

Count the $c|S|$ edges leaving $S$. For each vertex of $N(S)$ mark one of its edges into $S$; at least $c(1 - \varepsilon)|S|$ edges are marked, so at most $\varepsilon c|S|$ are not, and every vertex of $N(S) \setminus U(S)$ carries an unmarked edge. Hence $|U(S)| \ge c(1 - \varepsilon)|S| - \varepsilon c|S|$.

The same count gives a form without regularity: if every left vertex has at most $c$ neighbours, then each unique neighbour absorbs one of the at most $c|S|$ edges leaving $S$ and every other neighbour at least two, so $2|N(S)| \le |U(S)| + c|S|$. Hence $|N(S)| \ge \alpha|S|$ implies $|U(S)| \ge (2\alpha - c)|S|$, which for $\alpha = c(1 - \varepsilon)$ is the bound above.

## Sources

- V. Guruswami, A. Rudra, M. Sudan, "Essential Coding Theory", draft book, version of 26 August 2025, Section 11.3.1, Lemma 11.3.4 (with Definition 11.2.2 and Definition 11.3.3).
- M. Sipser, D. A. Spielman, "Expander Codes", IEEE Transactions on Information Theory, 1996.
