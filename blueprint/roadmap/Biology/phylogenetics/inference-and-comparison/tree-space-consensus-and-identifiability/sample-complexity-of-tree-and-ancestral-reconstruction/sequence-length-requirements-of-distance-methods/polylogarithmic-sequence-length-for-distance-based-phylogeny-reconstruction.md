# Polylogarithmic sequence length for distance-based phylogeny reconstruction

**Setting.** A phylogeny on $n$ leaves is a rooted binary tree with edge weights $w_e$ (branch lengths). Sequences of length $k$ evolve along it under a general time-reversible (GTR) substitution model with rate matrix $Q$ on $r\ge2$ states, sites i.i.d. The reconstruction problem asks to recover the tree topology from the leaf sequences with high probability. A method is *distance-based* if it uses only the pairwise sequence correlations between leaves. In the $\Delta$-branch model $\mathcal Y^{f,g}_\Delta\otimes\{Q\}$, all branch lengths satisfy $f\le w_e\le g$ and are integer multiples of $\Delta$, with $0<\Delta\le f\le g$. Let $g^*=\ln\sqrt2$, the Kesten–Stigum threshold in these units.

**Theorem.** For every $r\ge2$, every rate matrix $Q$ in the class $\mathcal Q_\varphi$ (reversible, with $Q_{ij}>0$ for all $i\ne j$, and normalized so that its second-largest eigenvalue is $\Lambda_2=-1$) and all $0<\Delta\le f\le g<g^*$, there is a distance-based method that solves the phylogenetic reconstruction problem on $\mathcal Y^{f,g}_\Delta\otimes\{Q\}$ with sequence length

$$k=\mathrm{poly}(\log n),$$

the dependence on $\Delta$ being of order $\Delta^{-2}$. Previously known distance-based methods (e.g. Erdős–Steel–Székely–Warnow) required $k=\mathrm{poly}(n)$ for general $f\le g$, while $k=O(\log n)$ in this regime was known only for non-distance methods based on explicit ancestral reconstruction, and for the CFN model.

**Weighted majority (GTR version).** For leaf states encoded by the eigenvector statistic $\sigma_x$ of $Q$ with correlation decay $\Theta_{\rho,x}$ along the root–leaf path, and any unit flow $\Psi$ from the root $\rho$ to the leaves, the estimator $S=\sum_x\Psi(x)\sigma_x/\Theta_{\rho,x}$ satisfies $\mathbb E[S\mid\sigma_\rho]=\sigma_\rho$ and $\mathrm{Var}[S]=1+K_\Psi$ with $K_\Psi=\sum_eR_\rho(e)\Psi(e)^2$; in the Kesten–Stigum zone $K_\Psi$ stays bounded, so the root state is linearly reconstructible.

## Expansion

Distances between deep internal vertices cannot be estimated directly from two leaf sequences with short sequences, because correlations decay exponentially in path length. The method instead averages leaf-to-leaf correlations over the subtrees below two internal vertices with the weighted-majority weights; this implicitly reconstructs the ancestral states linearly and gives distance estimates between deep vertices accurate to $\varepsilon$ with $k>\log^\kappa n$, together with a test that detects large distances. Discretized branch lengths let these approximate distances be rounded exactly, so the tree can be built level by level from the leaves upward.

## Sources

- Sebastien Roch, "Sequence-Length Requirement of Distance-Based Phylogeny Reconstruction: Breaking the Polynomial Barrier", arXiv:0908.2061 (2009), Section 1 (Definition 4, the class $\mathcal Q_\varphi$; Theorems 1–3, the $\Delta$-branch model) and Section 2 (Propositions 1–3), <https://doi.org/10.48550/arXiv.0908.2061>.
