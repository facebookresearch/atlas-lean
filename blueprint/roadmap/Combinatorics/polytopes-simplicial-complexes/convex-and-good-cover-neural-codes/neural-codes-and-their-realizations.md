# Neural codes and their realizations

A neural code is a set of subsets of the neurons, read as the patterns of neurons active together; a collection of sets in a stimulus space realizes it when exactly these patterns occur as the regions the sets cut out.

Let $[n] = \{1, \dots, n\}$. A *neural code* $\mathcal{C}$ on $n$ neurons is a subset of $2^{[n]}$; its elements are *codewords*, and the codewords maximal under inclusion are the *maximal codewords*. A collection $\mathcal{U} = \{U_1, \dots, U_n\}$ of sets in a stimulus space $X \subseteq \mathbb{R}^d$ *realizes* $\mathcal{C}$ if for every $\sigma \subseteq [n]$

$$
\sigma \in \mathcal{C} \iff \bigcap_{i \in \sigma} U_i \setminus \bigcup_{j \notin \sigma} U_j \neq \emptyset ,
$$

the empty intersection being $X$. So the empty set is a codeword exactly when some point of $X$ lies in none of the $U_j$.

Every neural code can be realized by open sets, as the source recalls. A finite code is given by listing its codewords.

## Depends on

None.

## Proof depends on

None.

## Sources

- Aaron Chen, Florian Frick and Anne Shiu, *Neural codes, decidability, and a new local obstruction to convexity*, SIAM Journal on Applied Algebra and Geometry 3 (2019), no. 1, 44–66, https://doi.org/10.1137/18M1186563; read as arXiv:1803.11516v2: Definition 2.1, Remark 2.5 (the empty codeword) and the remarks after Remark 2.2.
