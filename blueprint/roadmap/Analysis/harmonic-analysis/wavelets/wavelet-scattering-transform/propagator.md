# Scattering propagator

For maps $U[\lambda] : X \to X$ indexed by $\lambda \in \Lambda$ and a path $p = (\lambda_1, \dots, \lambda_m)$, the scattering propagator is the path-ordered product

$$U[p] = U[\lambda_m] \cdots U[\lambda_2]\, U[\lambda_1], \qquad U[\emptyset] = \mathrm{Id}$$

(S. Mallat, *Group invariant scattering*, Comm. Pure Appl. Math. 65 (2012), 1331–1398 (arXiv:1101.2286), Definition 2.2, equation (15)). The first index of the path acts first, so $U[p + p'] = U[p']\, U[p]$ for the concatenation $p + p'$ (equation (17)). In Mallat's scattering $U[\lambda] f = |f \star \psi_\lambda|$ and $U[p] f = |\,|f \star \psi_{\lambda_1}| \star \psi_{\lambda_2}| \cdots \star \psi_{\lambda_m}|$ (equation (16)); here the maps are arbitrary, and paths of length $m$ are functions $\{0, \dots, m-1\} \to \Lambda$.
