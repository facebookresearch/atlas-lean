# Statistical inconsistency of phylogeny reconstruction from $k$-mer counts

**Model.** Under the Cavender–Farris–Neyman (CFN) model, a binary root sequence of length $m$ with i.i.d. uniform sites evolves along the edges of a rooted tree $T$: each site flips independently at rate given by the edge lengths, and sites evolve independently. For a fixed $k \in \mathbb N$, the *$k$-mer frequency vector* of a leaf sequence counts the occurrences of each of the $2^k$ words of length $k$ among its $m-k+1$ (overlapping) windows. Let $\mathcal L^{(i)}_m$ be the joint law of the $k$-mer frequency vectors of all $n$ leaf sequences of length $m$ when the tree is $T_i$.

**Theorem.** Fix $k \in \mathbb N$. For every $n \ge 3$ there exist distinct trees $T_1 \neq T_2$ with $n$ leaves, which can be chosen independently of $k$, such that

$$\limsup_{m\to\infty}\ \big\|\mathcal L^{(1)}_m - \mathcal L^{(2)}_m\big\|_{\mathrm{TV}} < 1.$$

Consequently there is $\varepsilon > 0$ such that every estimator that sees only the $k$-mer counts of the whole leaf sequences recovers the correct tree with probability at most $1-\varepsilon$, uniformly in $m \ge k$: no alignment-free method based solely on full-sequence $k$-mer counts is statistically consistent, even as the sequence length tends to infinity. (The result does not cover block decompositions, which count $k$-mers in separate blocks.)

## Expansion

The trees differ only in the placement of the edge to one leaf $A$ among three leaves $\{A,B,C\}$ at equal distance from the root. The Markov property reduces the comparison to three sequences; $k$-mer counts are functions of counts of adjacent non-overlapping $k$-mer pairs, which satisfy linear flow constraints. After removing the redundancy, the non-redundant pair counts are sums of i.i.d. lattice vectors, and a multivariate local central limit theorem shows that their laws under the two trees are both approximately Gaussian with overlapping supports at the $\sqrt m$ scale, so the total variation distance stays bounded away from $1$.

## Sources

- Wai-Tong Louis Fan, Brandon Legried and Sebastien Roch, "Impossibility of phylogeny reconstruction from $k$-mer counts", arXiv:2010.14460 (2020), Theorem 1 and its proof sketch (reductions and local central limit theorem, Theorem 2 quoting Davis and McDonald), <https://doi.org/10.48550/arXiv.2010.14460>.
