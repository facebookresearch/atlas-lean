# Multiclass partial concept classes with boundedly many labels

Fix $k \in \mathbb{N}$ and let $H \subseteq \{0, 1, \dots, k, \star\}^X$ be a multiclass partial concept class, learned from distributions on $X \times \{0, 1, \dots, k\}$ that are realizable by $H$ (every finite sample is realized by some concept on its support). Then $H$ is PAC learnable if and only if its Natarajan dimension $\mathrm{Ndim}(H)$, defined through realizable label patterns, is finite, and the optimal sample complexity satisfies

$$
C_1\,\frac{\mathrm{Ndim}(H) + \log(1/\delta)}{\varepsilon} \le M(\varepsilon, \delta) \le C_2\,\frac{\mathrm{Ndim}(H)\log(k)}{\varepsilon}\log\frac{1}{\delta}
$$

for absolute constants $C_1, C_2$. Moreover, partial classes need not be captured by total ones: for every $k$ there is $H \subseteq \{0, \dots, k, \star\}^{\mathbb{N}}$ with $\mathrm{Ndim}(H) = O_k(1)$ all of whose disambiguations have infinite Natarajan dimension.

## Proof sketch

The lower bound is the usual shattering argument. For the upper bound, uniform convergence and ERM are unavailable, so one runs the one-inclusion hypergraph algorithm on the projection of $H$ to the sample and the test point; with $k + 1$ labels its orientations have out-degree $O(\mathrm{Ndim}(H)\log k)$, which bounds the leave-one-out error, and confidence is boosted as in the binary partial case. The disambiguation lower bound extends the binary construction of Alon, Hanneke, Holzman and Moran using Sauer's lemma for the growth function.

## Depends on

- [Partial concept classes and their VC and Littlestone dimensions](partial-concept-class.md)
- [N-shattering](../../../../../not-yet-classified/natarajan/nshatters.md)
- [Disambiguations of partial concept classes](disambiguation.md)

## Proof depends on

- [VC dimension characterizes PAC learnability of partial concept classes](partial-class-pac-characterization.md)
- [A partial class of VC dimension one with no finite-VC disambiguation](vc-one-partial-class-without-disambiguation.md)
- [One-inclusion hypergraphs, orientations and out-degree](../list-learning-and-multiclass-pseudo-cubes/one-inclusion-hypergraph.md)

## Sources

- A. Kalavasis, G. Velegkas, A. Karbasi, "Multiclass Learnability Beyond the PAC Framework: Universal Rates and Partial Concept Classes", NeurIPS (2022), arXiv:2210.02297, Definition 4, Theorems 3, 4 (Theorem 15) and 6.
