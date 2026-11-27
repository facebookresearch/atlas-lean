# Stacked reticulations and local modifications of DAG models

**Displayed tree model.** Let $G = (V,D)$ be a DAG (root: indegree 0; leaves: outdegree 0; tree vertices: indegree 1; reticulations: indegree $> 1$), with a random variable $X_v$ on a common state space $\Sigma$ at each vertex, internal ones hidden. Each edge $u \to v$ carries a transition matrix from a family $TM$; a reticulation $v$ selects one parent $u$ with reticulation probability $\gamma_{uv}$ and inherits along that edge, so $p(x_v \mid x_{\mathrm{pa}(v)}) = \sum_{u} \gamma_{uv} M^{uv}_{x_u x_v}$. The model is the DAG graphical model with these structured conditionals, marginalized to the leaves.

**Closure conditions on $TM$.** Multiplicatively closed; closed under convex combinations and marginal convex combinations; *splittable* (for any $M^1,\dots,M^k \in TM$ there is $N \in TM$ with $M^iN^{-1} \in TM$ for all $i$). All general equivariant models (open or not) and the Jukes-Cantor family $\{\exp(Q^{JC}t)\}$ satisfy them.

**Theorem (local modification).** If two DAGs differ only in a local structure $(A,B,C)$ versus $(A,B',C)$ (hidden vertices $B$, $B'$ between parents $A$ and children $C$), the induced families of conditionals $p(x_C \mid x_A)$ coincide, and every other conditional family is shared, then the two DAG models give the same family of distributions on the observed variables.

**Theorem (stacked reticulations).** Suppose $G$ has an edge $b \to c$ with $b$ of outdegree 1 and $X_b$ hidden, and let $G'$ contract it (each $a \to b$ becomes $a \to c$). If $TM$ is multiplicatively closed, closed under convex combinations and splittable, then the displayed tree models on $G$ and $G'$ have the same distribution family, also when all reticulation probabilities are required positive.

**Propositions (2-blobs).** A non-root 2-blob (a biconnected piece with one edge in and one out) whose vertices are hidden can be replaced by a single edge, and a root 2-blob by a cherry from a new hidden root, without changing the model. Hence stacked reticulations and 2-blobs are not identifiable from leaf distributions.

## Expansion

Locally, a stacked pair of reticulations composes two mixtures of transition matrices; closure under products and convex combinations says this is again a mixture of the allowed type, and splittability lets a common factor $N$ be pulled out of several edge matrices, so a two-step path through the hidden vertex can be rewritten as a single edge. So the conditional law of $X_c$ given its ancestors is the same set of kernels in $G$ and $G'$, and the local modification theorem transfers equality to the full joint law.

## Sources

- S. Sullivant, "Phylogenetic network models as graphical models", *Bulletin of Mathematical Biology* 88(8) (2026), 136, Section 3, Propositions 3.8-3.12, Theorem 4.4, Theorem 5.1 and Propositions 5.4, 5.6, <https://doi.org/10.1007/s11538-026-01695-3> (preprint arXiv:2507.23056).
