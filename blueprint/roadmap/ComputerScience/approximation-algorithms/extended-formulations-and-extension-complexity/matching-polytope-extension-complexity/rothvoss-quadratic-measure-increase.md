# Rothvoss' quadratic measure increase for cut-matching rectangles

Let $k \ge 3$ and $m$ be odd integers, $n=3m(k-3)+2k$, $t=\tfrac{m+1}{2}(k-3)+3$, and let $\mathcal{U}_{\mathrm{all}}$ be the $t$-element vertex subsets and $\mathcal{M}_{\mathrm{all}}$ the perfect matchings of $K_n$. For $U \subseteq V$ let $\delta(U)$ be the set of edges with exactly one endpoint in $U$ (the edges crossing the cut at $U$), and for $\ell \ge 0$ let $Q_\ell=\{(U,M) \in \mathcal{U}_{\mathrm{all}} \times \mathcal{M}_{\mathrm{all}} : |\delta(U) \cap M|=\ell\}$, the pairs at which the odd-cut slack $|\delta(U) \cap M|-1$ equals $\ell-1$. Since $t$ is odd and $|\delta(U) \cap M| = t-2|M \cap E(U)|$, the layer $Q_\ell$ is empty for even $\ell$; for $\ell \in \{1,3,k\}$ it is nonempty, and $\mu_\ell$ denotes the uniform probability measure on $Q_\ell$. There is $\delta=\delta(k) > 0$ such that every rectangle $\mathcal{R}=\mathcal{U} \times \mathcal{M}$ with $\mathcal{U} \subseteq \mathcal{U}_{\mathrm{all}}$, $\mathcal{M} \subseteq \mathcal{M}_{\mathrm{all}}$ and $\mu_1(\mathcal{R})=0$ satisfies

$$
\mu_3(\mathcal{R}) \le \frac{400}{k^2}\,\mu_k(\mathcal{R})+2^{-\delta m}.
$$

## Proof sketch

Following Razborov's corruption argument for disjointness, sample a random partition of $V$ into blocks $A_1,\dots,A_m$ of size $k-3$, two $k$-sets $C,D$, and blocks $B_1,\dots,B_m$ of size $2(k-3)$, and restrict to cuts made of whole $A$-blocks plus part of $C$ and matchings inside the blocks and $C \cup D$. Conditioned on the partition, cuts and matchings become nearly independent product structures, and the absence of $Q_1$ entries forces the rectangle's matchings on $C \cup D$ to be spread. Comparing how many ways a pair in $Q_3$ versus $Q_k$ can arise across $C \cup D$ yields the quadratic factor $k^2$, while partitions where the estimate fails have total measure $2^{-\delta m}$.

## Depends on

- [Perfect matching polytope](../../../../GraphTheory/matchings-and-flows/matching-polytope/perfect-matching-polytope.md)
- [Edges crossing a cut](../../../../GraphTheory/directed-graphs/modular-orientations/crosses-cut.md)
- [Odd-cut slack matrix of the perfect matching polytope](odd-cut-matching-slack.md)

## Proof depends on

- [Randomized communication complexity of disjointness](../../../../TheoryOfComputation/communication-complexity/randomized-communication-protocols/rand-complexity-disj-fn-ge.md)

## Sources

- Thomas Rothvoss, "The Matching Polytope has Exponential Extension Complexity", STOC (2014) and Journal of the ACM (2017), arXiv:1311.2369, Section 2 and Lemma 7.
- Alexander A. Razborov, "On the Distributional Complexity of Disjointness", Theoretical Computer Science (1992).
