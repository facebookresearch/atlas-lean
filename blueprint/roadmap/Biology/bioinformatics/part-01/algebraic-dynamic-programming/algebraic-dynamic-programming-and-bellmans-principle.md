# Algebraic dynamic programming and Bellman's principle

**Definition 1 (algebraic dynamic programming).** An ADP problem is specified by a signature $\Sigma$ over an input alphabet $\mathcal{A}$, a tree grammar $\mathcal{G}$ over $\Sigma$, and a $\Sigma$-evaluation algebra $\varepsilon$, which interprets each function symbol of $\Sigma$ as a function on a value set and carries an objective function $h$ mapping lists of values to lists of values. An instance is a string $w \in \mathcal{A}^*$; its search space $\mathcal{G}(w)$ is the set of trees of $\mathcal{G}$ whose yield is $w$ (for RNA folding, the candidate secondary structures of $w$). Solving the instance means computing

$$h\big[\, \varepsilon(t) \mid t \in \mathcal{G}(w) \,\big]$$

in time and space polynomial in $|w|$.

**Definition 2 (Bellman's principle).** An evaluation algebra satisfies Bellman's principle if, for every $k$-ary function $f$ in $\Sigma$ and all answer lists $z_1, \dots, z_k$,

$$h[\, f(x_1, \dots, x_k) \mid x_1 \leftarrow z_1, \dots, x_k \leftarrow z_k \,] = h[\, f(x_1, \dots, x_k) \mid x_1 \leftarrow h(z_1), \dots, x_k \leftarrow h(z_k) \,],$$

and $h(z \mathbin{+\!\!+} z') = h(h(z) \mathbin{+\!\!+} h(z'))$, where $\mathbin{+\!\!+}$ is list concatenation and $\leftarrow$ list membership.

When Bellman's principle holds, the yield parser can evaluate candidates bottom-up and apply $h$ to every intermediate list of alternatives without changing the result, which yields the usual polynomial dynamic programming recurrences derived mechanically from the grammar. Examples on the same grammar: base-pair maximization (objective $\max$), counting (objective summation, every candidate valued $1$), enumeration and pretty-printing (objective identity). With a non-redundant grammar the counting algebra returns the size of the search space in polynomial time, whereas the redundant Nussinov grammar assigns several trees to the same structure and overcounts.

## Depends on

- [The Nussinov recursion](../../nussinov-algorithm-for-rna-secondary-structure/nussinov.md)

## Expansion

The definition separates the search space (the grammar) from scoring (the algebra) and from the choice (the objective), so that one grammar can be reused with many algebras. The first identity of Definition 2 says that choosing early among the alternatives for subproblems loses nothing, and the second that choosing over a union can be done piecewise; together they let the objective be pushed inside the recursion. For minimization or maximization they amount to monotonicity of each evaluation function in each argument.

## Sources

- P. Steffen, R. Giegerich, "Versatile and declarative dynamic programming using pair algebras", BMC Bioinformatics 6 (2005) 224, Definitions 1-3 and Theorem 1, <https://doi.org/10.1186/1471-2105-6-224> (PMC1261154).
