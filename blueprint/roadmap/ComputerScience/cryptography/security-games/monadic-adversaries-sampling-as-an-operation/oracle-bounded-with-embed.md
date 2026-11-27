# Embedding keeps a two-phase query bound

Let $P$ be a signature, fix a sampling family, and let $\mathsf{cont}$ and $\mathsf{cont}'$ be predicates on outputs and natural numbers with

$$\forall x\ j,\ \mathsf{cont}(x, j) \implies \mathsf{cont}'(x, j).$$

For every budget $q$ and every computation $c$ over $P$ (without sampling) that satisfies the two-phase query bound with condition $\mathsf{cont}$ (at most $q$ queries along every path, and $\mathsf{cont}(x, j)$ at each output $x$ with $j$ queries of budget unused), its [embedding](embed.md) into the signature with sampling satisfies the oracle bound with budget $q$ and condition $\mathsf{cont}'$: at most $q$ oracle queries along every path, and $\mathsf{cont}'(x, j)$ at each output, with the same residual budget $j$.
