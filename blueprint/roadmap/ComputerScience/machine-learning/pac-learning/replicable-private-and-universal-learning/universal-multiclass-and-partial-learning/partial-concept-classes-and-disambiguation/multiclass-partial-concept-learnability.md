# Multiclass partial concept classes with boundedly many labels

Fix an integer $k \ge 1$ and let $H \subseteq \{0, 1, \dots, k, \star\}^X$ be a multiclass partial concept class, learned from distributions on $X \times \{0, 1, \dots, k\}$ that are realizable by $H$ (every finite sample is realized by some concept on its support). Then $H$ is PAC learnable if and only if its Natarajan dimension $\mathrm{Ndim}(H)$, defined through realizable label patterns, is finite. The optimal sample complexity satisfies, for all $\varepsilon, \delta \in (0,1)$,

$$
M_H(\varepsilon, \delta) \le C_2\,\frac{\mathrm{Ndim}(H)\log(k+1)}{\varepsilon}\log\frac{2}{\delta},
$$

and the lower bound holds in the worst case: for every $d \ge 1$ some class $H$ with $\mathrm{Ndim}(H) = d$ has $M_H(\varepsilon, \delta) \ge C_1 (d + \log(1/\delta))/\varepsilon$ for $\varepsilon, \delta$ below absolute constants, where $C_1, C_2 > 0$ are absolute constants. (A per-class lower bound fails: the class of the two constants on one point has $\mathrm{Ndim} = 1$ and is learned from one example.) Moreover, partial classes need not be captured by total ones: for every $k$ there is $H \subseteq \{0, \dots, k, \star\}^{\mathbb{N}}$ with $\mathrm{Ndim}(H) = O_k(1)$ all of whose disambiguations have infinite Natarajan dimension.

## Proof sketch

The lower bound is the usual shattering argument. For the upper bound, uniform convergence and ERM are unavailable, so one runs the one-inclusion hypergraph algorithm on the projection of $H$ to the sample and the test point; with $k + 1$ labels its orientations have out-degree $O(\mathrm{Ndim}(H)\log(k+1))$, which bounds the leave-one-out error, and confidence is boosted as in the binary partial case. The disambiguation lower bound extends the binary construction of Alon, Hanneke, Holzman and Moran using Sauer's lemma for the growth function.

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
