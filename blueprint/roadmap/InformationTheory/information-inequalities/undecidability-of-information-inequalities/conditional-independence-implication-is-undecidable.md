# Conditional independence implication is undecidable

No algorithm decides whether a finite list of conditional independence statements among random variables with finite support implies another such statement; this answers a question open since the semi-graphoid axioms of Pearl and Paz were shown incomplete.

For random variables $X_1, \dots, X_k$ and $\mathcal{U} \subseteq \{1, \dots, k\}$ write $X_{\mathcal{U}}$ for the tuple $(X_u)_{u \in \mathcal{U}}$, and $X_{\mathcal{U}} \perp X_{\mathcal{V}} \mid X_{\mathcal{W}}$ for [conditional independence](../../../Probability/random-fields/conditional-independence-on-finite-configuration/cond-indep.md) of $X_{\mathcal{U}}$ and $X_{\mathcal{V}}$ given $X_{\mathcal{W}}$.

**Theorem (Li).** The following problem is undecidable: given $k, l \in \mathbb{Z}_{>0}$ and sets $\mathcal{U}_i, \mathcal{V}_i, \mathcal{W}_i \subseteq \{1, \dots, k\}$ for $i = 0, \dots, l$, pairwise disjoint for each $i$, decide whether the implication

$$
\bigwedge_{i=1}^{l} \bigl( X_{\mathcal{U}_i} \perp X_{\mathcal{V}_i} \mid X_{\mathcal{W}_i} \bigr) \ \Longrightarrow\ X_{\mathcal{U}_0} \perp X_{\mathcal{V}_0} \mid X_{\mathcal{W}_0}
$$

holds for all jointly distributed random variables $X_1, \dots, X_k$ with finite support (Theorem 3 of the source).

The theorem also holds for discrete random variables with finite or countably infinite support. If all the variables have bounded cardinality the implication problem is decidable (Geiger and Meek; Niepert), and earlier work of the same author showed undecidability when only some variables have bounded cardinality.

## Depends on

- [Conditional independence for a finite weight](../../../Probability/random-fields/conditional-independence-on-finite-configuration/cond-indep.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Word consequences over all monoids and over finite monoids](../../../ComputerScience/databases/dependencies-and-the-chase/implication-proofs/monoid-word-consequences.md)

## Expansion

The proof follows Herrmann's undecidability proof for embedded multivalued dependencies and reduces from the uniform word problem for finite monoids: conditional independence constraints express a "Fano-non-Fano" condition (Section II of the source), and Section III represents endomorphisms of an abelian group by random variables, embedding finite monoids into endomorphism monoids, so that the implication holds exactly when the given relations imply the given equation in every finite monoid. Non-disjoint statements used in the construction are removed by an earlier reduction of the same author. The undecidability of the uniform word problem for finite monoids is Gurevich's theorem (reference [79] of the source). A good expansion links pages for the Fano-non-Fano condition and for the representation of finite monoids by random variables.

## Sources

- C. T. Li, "Undecidability of network coding, conditional information inequalities, and conditional independence implication", IEEE Transactions on Information Theory 69 (2023), no. 6, 3493–3510, https://doi.org/10.1109/TIT.2023.3247570; read in arXiv:2205.11461v3 (Theorem 3, its footnote, the introduction and Sections II and III of arXiv:2205.11461v3).
