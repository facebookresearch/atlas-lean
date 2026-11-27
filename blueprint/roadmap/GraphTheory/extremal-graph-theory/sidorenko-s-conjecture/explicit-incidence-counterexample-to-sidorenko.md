# Incidence graph violating the Sidorenko inequality

The fixed bipartite simple graph $H$ has vertex parts $\{0,\ldots,12\}$ and the following 22 indexed triples; each triple-vertex is joined precisely to its three elements:

$$
\begin{gathered}
013,019,023,029,\ (1,3,10),(1,7,10),(1,7,12),(1,9,12),\\
234,249,\ (3,4,11),(3,10,11),489,(4,8,11),567,(5,6,11),\\
(5,7,10),(5,10,11),(6,7,12),(6,8,11),(6,8,12),(8,9,12).
\end{gathered}
$$

Here a three-digit entry lists three single-digit elements. There exists a finite simple host $G$ with $N>0$ labelled vertices and at least one edge such that $t(H,G)<(2|E(G)|/N^2)^{66}$. The homomorphism density $t(H,G)$ is the number of all adjacency-preserving maps (not necessarily injective) divided by $N^{35}$.

## Depends on

- [Edge density as a homomorphism density](hom-density-top-fin-two.md)
- The explicit incidence pattern and normalization of finite graph homomorphism counts.

## Expansion

Separate the transfer to a finite simple host for this fixed incidence graph $H$. Take a finite nonempty set $\Omega$ with probability law $\pi$ and a symmetric function $U:\Omega\times\Omega\to[0,1]$. For independent $X,Y$ with law $\pi$, let $\mu=\mathbb E[U(X,Y)]>0$. With independent labels $(X_v)_{v\in V(H)}$ of that same law, let $\tau=\mathbb E[\prod_{\{u,v\}\in E(H)}U(X_u,X_v)]$. Assume the strict gap $\tau<\mu^{66}$. Under these assumptions obtain a finite simple host $G$ on $N>0$ vertices with positive edge density and $t(H,G)<(2|E(G)|/N^2)^{66}$. In the transfer, sample vertex labels from $\pi$ and, given the labels, sample each unordered edge independently with probability given by $U$. Control collisions and choose the host order using the strict gap before applying this transfer to a specific kernel witness.

## Proof outline

Verify the incidence table gives 35 vertices and 66 edges and bridge its homomorphism density to the existing API. Give the strict gap and the witness or limiting transfer as separate statements; do not replace this counterexample by a claim about the forcing conjecture.

## Sources

- [Comparator statement: `OAI.SidorenkoCounterexample.main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SidorenkoCounterexample.lean#L40-L44)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/161.md)
- [The finite probability kernel and its gap](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/Sidorenko/Symmetrization.lean#L109-L120), and [transfer to a finite host](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/Sidorenko/RandomHost.lean#L282-L306).
