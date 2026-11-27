# Gradient-flow structure of absorbing evolutionary Markov chains via the Q-process

**Setting.** Evolutionary chains such as the Moran process with $N$ individuals are reducible: the monomorphic states are absorbing. Call an $(N+1)\times(N+1)$ stochastic matrix $\mathbf{M}$ *admissible* (in $\mathcal{A}_{N+1,k}$, $1 \le k < N-1$) if, after a permutation,

$$ \mathbf{M} \simeq \begin{pmatrix} \widetilde{\mathbf{M}} & \mathbf{0}\\ \mathbf{A} & \mathbf{I}_k \end{pmatrix}, $$

with $\widetilde{\mathbf{M}}$ (the core, acting on transient states) irreducible and no row of $\mathbf{A}$ identically zero. The continuous-time chain evolves as $\dot{\mathbf{p}} = (\mathbf{M} - \mathbf{I})\mathbf{p}$. Let $\mu = \rho(\widetilde{\mathbf{M}})$, with positive left and right Perron eigenvectors $\widetilde{\mathbf{w}}, \widetilde{\mathbf{z}}$ normalized by $\langle\widetilde{\mathbf{w}},\mathbf{1}\rangle = \langle\widetilde{\mathbf{w}},\widetilde{\mathbf{z}}\rangle = 1$ (the *characteristic triple*).

**Q-process.** The kernel $\mathbf{K} = \mu^{-1}\operatorname{diag}(\widetilde{\mathbf{w}})^{-1}\widetilde{\mathbf{M}}^{\dagger}\operatorname{diag}(\widetilde{\mathbf{w}})$ is irreducible and row-stochastic, with unique stationary law $\boldsymbol{\pi} = \widetilde{\mathbf{w}}\circ\widetilde{\mathbf{z}}$. It is the chain conditioned never to be absorbed. If $\mathbf{M}$ is *micro-reversible*, meaning $\operatorname{diag}(\widetilde{\mathbf{w}})\widetilde{\mathbf{M}}\operatorname{diag}(\widetilde{\mathbf{z}})$ is symmetric, then $\mathbf{K}$ is reversible. Every admissible matrix with $k = 2$ absorbing states and tridiagonal core (birth–death chains such as the Moran process) is micro-reversible.

**Theorem.** Let $\mathbf{M}$ be admissible, with Q-process kernel $\mathbf{K}$ reversible (for instance, $\mathbf{M}$ micro-reversible). For a non-absorbed initial state, define the rescaled transient law

$$ \mathbf{q}(t) = \frac{\widetilde{\mathbf{w}}\circ\widetilde{\mathbf{p}}(t/\mu)}{\langle\widetilde{\mathbf{w}},\widetilde{\mathbf{p}}(t/\mu)\rangle}. $$

Then $\mathbf{q}$ is the gradient flow

$$ \frac{d\mathbf{q}}{dt} = -\operatorname{grad}_{\mathcal{W}_N} H(\mathbf{q}\,|\,\boldsymbol{\pi}) $$

of the relative entropy $H(\mathbf{q}|\boldsymbol{\pi}) = \sum_i q_i\log(q_i/\pi_i)$ with respect to Maas's discrete Wasserstein distance $\mathcal{W}_N$ built on $\mathbf{K}$. The full dynamics of $\mathbf{p}$, including the absorbed mass, is uniquely recovered from $\mathbf{q}$, since $\langle\widetilde{\mathbf{w}},\widetilde{\mathbf{p}}(t)\rangle$ decays exactly like $e^{-(1-\mu)t}$.

The Moran process is therefore a time-rescaled entropy-dissipating gradient flow after factoring out fixation, although the chain itself is irreversible and has no positive stationary distribution.

## Depends on

- [Moran process as a stochastic matrix](../../../moran-model/moran-matrix.md)

## Proof depends on

## Expansion

The absorbed components are slaved to the transient ones, and the weighted mass $\langle\widetilde{\mathbf{w}},\widetilde{\mathbf{p}}\rangle$ satisfies a closed linear ODE, because $\widetilde{\mathbf{w}}$ is a left eigenvector of $\widetilde{\mathbf{M}}$. Dividing it out (a Doob $h$-transform with $h = \widetilde{\mathbf{w}}$) turns the sub-stochastic transient dynamics into the mass-preserving reversible chain $\mathbf{K}$. Maas's theorem then identifies the forward equation of a reversible Markov chain with the discrete Wasserstein gradient flow of relative entropy with respect to its stationary law.

## Sources

- Fabio A. C. C. Chalub, Léonard Monsaingeon, Ana Margarida Ribeiro and Max O. Souza, "Gradient flow formulations of discrete and continuous evolutionary models: a unifying perspective", arXiv:1907.01681 (2019), Section 2: Definitions 1–3, Lemmas 2–3, Theorem 2 (gradient flow structure for reducible irreversible kernels), <https://doi.org/10.48550/arXiv.1907.01681>; published in *Acta Applicandae Mathematicae* 171 (2021), article 24, <https://doi.org/10.1007/s10440-021-00391-9>. Locators follow arXiv v2.
