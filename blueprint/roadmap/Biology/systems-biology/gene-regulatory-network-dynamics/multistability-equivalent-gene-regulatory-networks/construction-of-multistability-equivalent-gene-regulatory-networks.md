# Construction of multistability-equivalent gene regulatory networks

**Setting.** A low-dimensional gene-switch model

$$\Sigma_f:\ \dot z = f(z) = a(z) - kz, \qquad z \in \mathbb{R}_+^n,\ k = \mathrm{diag}(k_1,\dots,k_n) > 0,$$

has $R$ steady states $z^{*(r)}$, none with Jacobian eigenvalues on the imaginary axis, and a constant interaction sign matrix $S_a = \mathrm{sgn}(\partial a/\partial z)$. The structure of a larger gene regulatory network is known only qualitatively, through a sign matrix $S_A \in \{-1,0,1\}^{N \times N}$, $N \ge n$. A system

$$\Sigma_F:\ \dot x = F(x) = A(x) - D(x), \qquad x \in \mathbb{R}_+^N,$$

is **multistability-equivalent** to $\Sigma_f$ and consistent with $S_A$ if (i) $\mathrm{sgn}(\partial A/\partial x) = S_A$ on the open orthant; (ii) there is an injective map $h$ with $f(z^*) = 0 \iff F(h(z^*)) = 0$; and (iii) each pair of corresponding steady states $z^{*(r)}$, $h(z^{*(r)})$ has the same number of eigenvalues with positive real part. Equivalent systems thus have the same number of steady states with the same stability types.

**Assumptions.** (*Modular structure*) After reordering, the first $n$ variables are master genes and each remaining module gene $i$ belongs to the module of exactly one master gene $m_i$: it receives activation from at most that master gene and otherwise only nonnegative inputs from genes of the same module. (*Consistency*) For every nonzero entry $S_a|_{i,j}$ there is a simple path from $j$ to $i$ in the network of $S_A$ whose product of signs is $S_a|_{i,j}$, and every path from $j$ entering master gene $i$ through a module gene corresponds to a nonzero $S_a|_{i,j}$.

**Construction.** (1) Give each module gene linear dynamics $F_i(x) = \sum_j S_A|_{i,j}x_j - K_i x_i$ with gains $K_i > 0$ to be chosen. (2) Compute the transfer gains $G_{k \to i}(\lambda)$ from each master gene $x_k$ through its module and their static values. (3)–(4) Define the master-gene interaction functions from $a$, composed with maps between the state spaces built from these static gains, so that the gains of the added module paths are exactly compensated at steady state.

**Theorem.** Under the two assumptions, for any target structure $S_A$ there are thresholds $K_j^{\min}$, $j = n+1,\dots,N$, such that every system built by Steps 1–4 with $K_j > K_j^{\min}$ for all module genes is multistability-equivalent to $\Sigma_f$. This holds for networks with any number of internal feedback loops, broken into a multi-input multi-output (MIMO) loop-breaking system, generalising the earlier single-input single-output (SISO) result.

## Proof sketch

At steady state the module genes are linear in their master gene, so the construction makes the steady states of $\Sigma_F$ the images $h(z^*)$ of those of $\Sigma_f$. For stability, cut the feedback loops (loop breaking) so that the Jacobian's characteristic polynomial becomes a determinant of the identity minus an open-loop transfer matrix; large module gains $K_j$ make the module dynamics fast, so on any fixed contour avoiding the origin the open-loop transfer matrix of $\Sigma_F$ is close to that of $\Sigma_f$. The argument principle then forces both characteristic polynomials to have the same number of zeros in the right half plane. In the MIMO case the scalar return difference is replaced by a determinant, which is why several loops can be handled at once; the method is illustrated on a gene regulatory network for mesenchymal stem cell differentiation.

## Sources

- Daniella Schittler, Taouba Jouini, Frank Allgöwer and Steffen Waldherr, "Multistability equivalence between gene regulatory networks of different dimensionality with application to a differentiation network", *International Journal of Robust and Nonlinear Control* 26 (2016), 4148–4168, <https://doi.org/10.1002/rnc.3560>. Preprint version: arXiv:1312.7250 (2013), Definition of multistability equivalence, Assumptions 1–2, construction Steps 1–4 and the main theorem with its proof, <https://doi.org/10.48550/arXiv.1312.7250>.
