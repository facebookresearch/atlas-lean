# Hadamard conjugation and its inversion for group-based models

**Binary-symmetric case.** Consider the two-state symmetric (Cavender–Farris–Neyman) model on an unrooted phylogenetic tree $\mathcal T$ with leaves $\{0, 1, \dots, n-1\}$: along each edge $e$ the state flips at rate $1$ (rate matrix $Q = -I + K$ with $K$ the transposition), so after time $t_e$ the flip probability is $\tfrac12(1 - e^{-2t_e})$, and the root state is uniform. Index splits of the leaves by subsets $A \subseteq \{1, \dots, n-1\}$ (the side not containing leaf $0$). The **edge length spectrum** $\gamma$ has $\gamma_A = t_e$ if $A$ is the split of edge $e$, $\gamma_A = 0$ for splits not in $\mathcal T$, and $\gamma_\emptyset = -\sum_{A \ne \emptyset}\gamma_A$. The **sequence spectrum** $s$ has $s_B$ equal to the probability of the site pattern in which exactly the leaves in $B$ differ from leaf $0$. Let $H$ be the $2^{n-1} \times 2^{n-1}$ Sylvester–Hadamard matrix, $H_{AB} = (-1)^{|A \cap B|}$.

**Theorem (Hadamard conjugation).**

$$s = H^{-1}\exp(H\gamma), \qquad \gamma = H^{-1}\ln(Hs),$$

with $\exp$ and $\ln$ applied entrywise; the second formula applies to any sequence spectrum with $Hs > 0$. So the map from edge lengths to site-pattern probabilities is invertible, and the tree with its edge lengths can be read off from the pattern probabilities.

**General abelian group-based models.** Let the states form a finite abelian group $G$, let $K_\sigma$ be the permutation matrix of translation by $\sigma \in G$, and let every edge carry the Markov matrix $M_e = e^{Q_e}$ of a rate matrix $Q_e = -\lambda_e\mathbf 1 + \sum_{\sigma \ne 0}\alpha_e^\sigma K_\sigma$ with $\alpha_e^\sigma \ge 0$ and $\lambda_e = \sum_{\sigma\ne0}\alpha_e^\sigma$, as in the source. Then $M_e(g,h) = f_e(h - g)$ is invariant under translation by $G$ (Jukes–Cantor, Kimura 2ST and 3ST for $G = \mathbb Z_2 \times \mathbb Z_2$, the $\mathbb Z_r$ models). Applying the character table of $G$ at every leaf (the tensor power of the group's Fourier matrix) diagonalizes the model: the transformed pattern probabilities $\hat p(\chi_1, \dots, \chi_n)$, indexed by irreducible characters at the leaves, vanish unless $\prod_i \chi_i$ is trivial, and otherwise factor over the edges as

$$\hat p(\chi_1, \dots, \chi_n) = \prod_{e \in E(\mathcal T)} \hat f_e\Big(\prod_{i \in A_e}\chi_i\Big),$$

where $A_e$ is the set of leaves on one side of $e$ and $\hat f_e$ is the Fourier transform of $f_e$. Taking logarithms and inverting the leaf transform gives a one-to-one correspondence between pattern probabilities and the edge parameters $\alpha_e^\sigma$, generalizing the Hadamard conjugation. (For arbitrary translation-invariant Markov matrices the correspondence is not one-to-one: for $G = \mathbb Z_2$, swapping $p_e \leftrightarrow 1 - p_e$ on the three edges at an internal vertex leaves the leaf distribution unchanged.) The paper derives this correspondence by elementary matrix multiplication with rectangular matrices indexed by ordered set partitions of the leaves, and stresses that it relies on $G$ being abelian, so that all irreducible representations are one-dimensional.

## Expansion

For the binary model, $(Hs)_B$ is the expectation of $(-1)$ raised to the number of state changes on edges whose split $A_e$ meets $B$ in an odd number of leaves, so $(Hs)_B = \prod_{e:\,|A_e \cap B| \text{ odd}} e^{-2t_e}$, because changes on different edges are independent and each edge contributes the factor $1 - 2\cdot\tfrac12(1 - e^{-2t_e})$. Taking logarithms, $\ln(Hs)_B = -2\sum_{A:\,|A \cap B|\text{ odd}}\gamma_A = (H\gamma)_B$, using $\gamma_\emptyset = -\sum\gamma_A$. In the general case the projection operators of the irreducible representations, read off the character table, are the change of basis that turns each edge's group-invariant Markov matrix into a diagonal one, and the tree structure turns the joint transform into a product over edges. The same inversion underlies spectral analysis of phylogenetic data, likelihood on split networks, and the identifiability of tree mixtures.

## Sources

- Jeremy G. Sumner, Peter D. Jarvis, Barbara R. Holland, "A tensorial approach to the inversion of group-based phylogenetic models", arXiv (2012). Section 2 (phylogenetic tensors, connection to Fourier analysis), Section 3 (binary-symmetric case), Sections 4–6 ($\mathbb Z_3$, K3ST, $\mathbb Z_r$), Section 7 (any abelian group-based model). <https://doi.org/10.48550/arXiv.1212.3888>. Published version: BMC Evolutionary Biology 14(1) (2014), article 236, <https://doi.org/10.1186/s12862-014-0236-6>; locators above refer to the arXiv version.
- M. D. Hendy, D. Penny, "Spectral analysis of phylogenetic data", Journal of Classification 10 (1993), 5–24, <https://doi.org/10.1007/BF02638451>.
