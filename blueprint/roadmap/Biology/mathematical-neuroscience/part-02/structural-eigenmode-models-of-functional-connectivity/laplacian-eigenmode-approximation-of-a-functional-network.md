# Laplacian eigenmode approximation of a functional network

**Structural eigenmodes.** Let $A \in \mathbb{R}^{N \times N}$ be a symmetric non-negative structural connectivity matrix with node strengths $d_i = \sum_j a_{ij} > 0$ and $K_A = \mathrm{diag}(d_1, \dots, d_N)$. The Laplacian is $Q_A = K_A - A$ and its symmetric normalisation

$$Q_{As} = K_A^{-1/2} Q_A K_A^{-1/2} = Z\, \mathrm{diag}(\mu_1, \dots, \mu_N)\, Z^\top,$$

with $Z$ orthogonal (columns $z_i$ are the structural eigenmodes) and eigenvalues $\mu_i \in [0, 2]$. Since $Q_A \mathbf{1} = 0$, the eigenvalue $0$ has eigenvector

$$z_0 = \frac{K_A^{1/2} \mathbf{1}}{\|K_A^{1/2} \mathbf{1}\|} = \frac{1}{\sqrt{\sum_i d_i}} \bigl(\sqrt{d_1}, \dots, \sqrt{d_N}\bigr)^\top,$$

and eigenmodes with larger $\mu_i$ oscillate more strongly across the end nodes of edges (higher spatial frequency).

**Functional network.** For a symmetric non-negative functional connectivity matrix $W(t)$ at time $t$ (for example instantaneous amplitude correlation or a phase-locking measure) with strength matrix $K_W(t)$, define $Q_{Ws}(t) = K_W^{-1/2}(t)\,\bigl(K_W(t) - W(t)\bigr)\, K_W^{-1/2}(t)$.

**Eigenmode approximation.** Assume $Q_{Ws}(t) \approx Z P(t) Z^\top$ with $P(t)$ diagonal, i.e. the functional Laplacian shares the structural eigenbasis. Then

$$W_{\mathrm{apx}}(t) = K_W(t) - K_W^{1/2}(t)\, Z P(t) Z^\top K_W^{1/2}(t),$$

and the least-squares weights

$$P(t) = \arg\min_{P \text{ diagonal}} \bigl\| Q_{Ws}(t) - Z P Z^\top \bigr\|_F$$

are the Rayleigh quotients $P(t) = \mathrm{diag}\bigl(z_1^\top Q_{Ws}(t) z_1, \dots, z_N^\top Q_{Ws}(t) z_N\bigr)$.

## Expansion

$Q_{As} K_A^{1/2} \mathbf{1} = K_A^{-1/2} Q_A \mathbf{1} = 0$ gives the zero mode. For the weights, orthogonal invariance of the Frobenius norm gives $\|Q_{Ws} - Z P Z^\top\|_F = \|Z^\top Q_{Ws} Z - P\|_F$, and among diagonal matrices the closest one to $Z^\top Q_{Ws} Z$ is its diagonal, whose entries are $z_i^\top Q_{Ws} z_i$. The approximation is exact precisely when $Z$ diagonalises $Q_{Ws}(t)$ (equivalently, when the structural eigenvalues are distinct, when $Q_{Ws}(t)$ commutes with $Q_{As}$), so the residual measures how far the functional network departs from a function of the structural Laplacian. Restricting $P(t)$ to a subset of eigenmodes identifies which structural spatial frequencies carry the time-varying functional interactions; in resting-state MEG, amplitude connectivity is captured by structural eigenmodes better than phase connectivity, and both far better than by direct structural links.

## Sources

- P. Tewarie, B. Prasse, J. Meier, et al., "Predicting time-resolved electrophysiological brain networks from structural eigenmodes", Human Brain Mapping 43 (2022) 4475–4491, Section 2.5, Equations (3)–(6), <https://doi.org/10.1002/hbm.25967> (PMC9435022).
