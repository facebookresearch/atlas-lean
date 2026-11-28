# Segregating-site to phylogenetic-diversity transform

Let $T$ be a phylogenetic tree on the taxon set $X$ with branch lengths, and let bi-allelic sites evolve on $T$ under the symmetric two-state model: the root state is uniform on $\{0,1\}$ and a branch of length $t$ changes the state with probability $\tfrac12(1 - e^{-2t})$. Let $s_A$ be the probability that a site segregates (is non-constant) over $A \subseteq X$ and $\delta_A$ the phylogenetic diversity of $A$, the total length of the smallest subtree of $T$ spanning $A$. Let $\boldsymbol{\delta}$ and $\mathbf{s}$ be the vectors of $\delta_A$ and $s_A$ over nonempty subsets $A$ of even cardinality. Then (Theorem 7)

$$
\boldsymbol{\delta} = -\mathbf{G}\,\log\!\left(\mathbf{1} - \mathbf{G}^{-1}\mathbf{s}\right),
$$

with the logarithm taken entrywise, where $\mathbf{G}$ is indexed by even subsets and does not depend on $T$:

$$
\mathbf{G}_{AB} = \begin{cases} 2^{-|A|+1}, & B \subseteq A, \\ 0, & \text{otherwise}, \end{cases} \qquad (\mathbf{G}^{-1})_{AB} = \begin{cases} 2^{|B|-1}\,\mathbb{E}_{|A|-|B|}, & B \subseteq A, \\ 0, & \text{otherwise}, \end{cases}
$$

and $\mathbb{E}_k$ are the Euler numbers, $1/\cosh x = \sum_{k \ge 0} \mathbb{E}_k x^k/k!$. The transform is invertible, so the vector of even-subset segregation probabilities determines the vector of even-subset phylogenetic diversities and conversely, without knowledge of $T$.

The proof passes through two intermediate quantities defined for even $A$: $\gamma_A$, the probability that an odd number of taxa in $A$ carry state 1, and $\mu_A$, the length of the path-set of $T$ with endpoint set $A$ (the edge set of a disjoint union of leaf-to-leaf paths pairing up $A$). For $|A|$ even (Theorems 5 and 6),

$$
\gamma_A = \frac14 \sum_{\substack{B \subseteq A\\ |B| \text{ even}}} 2^{|B|}\,\mathbb{E}_{|A|-|B|}\, s_B, \qquad \mu_A = \frac14 \sum_{\substack{B \subseteq A\\ |B| \text{ even}}} 2^{|B|}\,\mathbb{E}_{|A|-|B|}\, \delta_B,
$$

and Hendy's path-set identity for the symmetric model gives $\mu_A = -\tfrac12 \log(1 - 2\gamma_A)$.

## Depends on

- [Even-subset determination of segregating sites and phylogenetic diversity](even-subset-determination-of-segregating-sites-and-phylogenetic-diversity.md)

## Expansion

In vector form the linear steps read $\boldsymbol{\gamma} = \tfrac12 \mathbf{G}^{-1}\mathbf{s}$ and $\boldsymbol{\delta} = 2\mathbf{G}\boldsymbol{\mu}$; inserting the path-set identity gives the transform. For a pair $A = \{a,b\}$ it reduces to $\delta_{ab} = -\tfrac12 \log(1 - 2 s_{ab})$, the two-state distance correction applied to the probability that $a$ and $b$ differ. The transform is the diversity analogue of the Hendy–Penny Hadamard transform, which maps split weights to pattern probabilities; it can also be obtained by converting diversities to split weights, applying the Hadamard transform, and converting pattern probabilities to segregating-site probabilities. It thus links Watterson-type segregating-site measures of population genetics with Faith's phylogenetic diversity of conservation biology.

## Sources

- David Bryant, Steffen Klaere, The link between segregation and phylogenetic diversity, arXiv:1008.4625 (2010). <https://doi.org/10.48550/arXiv.1008.4625>. Published version: Journal of Mathematical Biology 64(1-2) (2012), 149–162, <https://doi.org/10.1007/s00285-011-0409-5>; locators above refer to the arXiv version.
