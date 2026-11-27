# Exact linear lumping of rational dynamical systems

**Definitions.** Consider $\dot{\mathbf x} = \mathbf f(\mathbf x)$, $\mathbf x \in \mathbb{R}^n$, with rational right-hand side $\mathbf f \in \mathbb{R}(\mathbf x)^n$ (e.g. Michaelis–Menten or Hill kinetics in a biochemical model). A linear map $\mathbf y = L\mathbf x$ with $L \in \mathbb{R}^{m \times n}$ of rank $m$ is a **lumping** of dimension $m$ if there are rational functions $g_1,\dots,g_m \in \mathbb{R}(\mathbf y)$ with

$$L\,\mathbf f(\mathbf x) = \mathbf g(L\mathbf x),$$

so the macro-variables $\mathbf y$ obey the self-contained system $\dot{\mathbf y} = \mathbf g(\mathbf y)$. Given observables $\mathbf x_{\mathrm{obs}} = M\mathbf x$ ($M \in \mathbb{R}^{p \times n}$), a lumping is **constrained** if every observable is a linear combination of the entries of $\mathbf y$. Partition-based lumpings ($y_j = \sum_{i \in S_j} x_i$ over a partition of the variables) are constrained lumpings whose only observable is the total $\sum_i x_i$.

**Invariant-subspace characterisation.** With $J(\mathbf x)$ the Jacobian of $\mathbf f$, $L$ is a lumping iff the row space of $L$ is invariant under right multiplication by $J(\mathbf x)$ for every $\mathbf x$ in the domain, i.e. $\mathrm{rowspan}(L\,J(\mathbf x)) \subseteq \mathrm{rowspan}(L)$ for all $\mathbf x$. Consequently the constrained lumping of minimal dimension is unique: its row space is the smallest subspace containing the rows of $M$ and invariant under all $J(\mathbf x)$.

**Proposition (randomised algorithm).** Writing $J(\mathbf x) = \sum_k J_k\,m_k(\mathbf x)$ over linearly independent rational functions $m_k$, the minimal invariant subspace is the smallest subspace containing $\mathrm{rowspan}(M)$ and invariant under the constant matrices $J_k$, equivalently under the matrices $J(\mathbf x_1),\dots,J(\mathbf x_s)$ for sufficiently many generic evaluation points. An evaluation–interpolation algorithm that samples such points returns the minimal constrained lumping with probability at least $1 - \varepsilon$, for any prescribed $\varepsilon > 0$, and the sampling routine produces with probability at least $1 - \varepsilon$ enough points for the spaces spanned by the evaluated Jacobians and by the $J_k$ to coincide.

## Proof sketch

Differentiating $L\mathbf f(\mathbf x) = \mathbf g(L\mathbf x)$ gives $L J(\mathbf x) = J_{\mathbf g}(L\mathbf x)\,L$, so each row of $LJ(\mathbf x)$ is a combination of rows of $L$; conversely, invariance makes $L\mathbf f$ constant along the fibres of $L$, so it factors through $L\mathbf x$. Invariance under a family of matrices is closed under intersection, which gives a unique minimal subspace, computable by repeatedly multiplying the current basis by the matrices and orthogonalising until the dimension stabilises. For polynomial dynamics (the earlier CLUE algorithm) the coefficient matrices $J_k$ can be read off from the monomial expansion; for rational dynamics the paper works with evaluations of the Jacobian at sampled points instead. The method can find reductions that embedding the rational system into a larger polynomial one misses, as in models of Michaelis–Menten kinetics with competing substrates and of nerve growth factor signalling.

## Sources

- Antonio Jiménez-Pastor, Joshua Paul Jacob and Gleb Pogudin, "Exact Linear Reduction for Rational Dynamical Systems", in *Lecture Notes in Computer Science*, Springer International Publishing, 2022, 198–216, <https://doi.org/10.1007/978-3-031-15034-0_10>. Preprint version: arXiv:2201.13373 (2022), Section 2 (definitions of lumping and constrained lumping, the invariant-subspace correspondence) and Section 3 (the correctness propositions for the main and sampling algorithms), <https://doi.org/10.48550/arXiv.2201.13373>.
