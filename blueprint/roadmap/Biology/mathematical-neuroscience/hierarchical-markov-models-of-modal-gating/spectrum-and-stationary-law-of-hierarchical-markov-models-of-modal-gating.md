# Spectrum and stationary law of hierarchical Markov models of modal gating

**Setting.** Many ion channels switch spontaneously between *modes* of different activity, and within each mode open and close with mode-specific kinetics. A continuous-time hierarchical Markov model combines: a top-level generator $M$ on $\sum_i m_i$ states, block-partitioned into modes $M^{i,j}$ ($i,j = 1,\dots,n_M$), and for each mode $i$ a generator $Q^i$ on $n_i$ gating states with an entry distribution $p^i$ (a row vector). With the Kronecker product $\otimes$ and Kronecker sum $A \oplus B = A \otimes I + I \otimes B$, the full generator has blocks

$$\mathcal M^{i,i} = M^{i,i} \oplus Q^i, \qquad \mathcal M^{i,j} = M^{i,j} \otimes P^{i,j}, \quad P^{i,j} = \mathbf 1_{n_i}\,p^j \ (i \ne j),$$

so that within a mode both levels evolve independently, and on switching from mode $i$ to mode $j$ the gating chain restarts from $p^j$. Initial laws are pure tensors $v^i \otimes w^i$ on each mode block.

**Theorem.**

1. *(Spectrum.)* Every eigenvalue of $M$ is an eigenvalue of the full generator $\mathcal M$, and so is every $\mu + \lambda$ with $\mu$ an eigenvalue of $M^{i,i}$ and $\lambda \ne 0$ an eigenvalue of $Q^i$. Under detailed balance, if $v$ is a right eigenvector of $M$ for $\mu$, then $v \otimes \mathbf 1$ is a right eigenvector of $\mathcal M$ for $\mu$.
2. *(Modal sojourn times.)* The sojourn-time density in mode $i$ of the full model equals that of the top-level model $M$ in its aggregate $i$.
3. *(Stationary law.)* If each entry distribution is the stationary law of its mode, $p^i = \bar q^i$, then from an initial law $v^0 \otimes \bar q$ the solution stays a product, $p(t) = (v^1(t)\otimes\bar q^1;\dots;v^{n_M}(t)\otimes\bar q^{n_M})$, and the full model has stationary distribution $(\bar m^1 \otimes \bar q^1;\dots;\bar m^{n_M}\otimes\bar q^{n_M})$, where $\bar m$ is stationary for $M$; if $v(t)\to\bar m$ (for instance when $M$ is irreducible), then $p(t)$ converges to this product law.

## Expansion

Within a mode the generator is a Kronecker sum, whose eigenvalues are sums of the eigenvalues of its parts; mode switching couples blocks only through rank-one restarts $\mathbf 1\,p^j$, which act trivially on vectors orthogonal to the constant direction of each gating chain. A Schur decomposition adapted to this block structure therefore separates the slow mode-switching spectrum (inherited from $M$) from the fast within-mode spectrum. Biologically, mode dwell times are governed by the top-level model alone, so mode switching and gating kinetics can be fitted separately from single-channel recordings and then combined, as done for the inositol trisphosphate receptor.

## Sources

- Ivo Siekmann, Mark Fackrell, Edmund J. Crampin and Peter Taylor, "Modelling modal gating of ion channels with hierarchical Markov models", Proceedings of the Royal Society A: Mathematical, Physical and Engineering Sciences 472 (2016), 20160122, <https://doi.org/10.1098/rspa.2016.0122>; numbering as in arXiv:1602.05877: Definition 2.5 and Propositions 4.1–4.4.
