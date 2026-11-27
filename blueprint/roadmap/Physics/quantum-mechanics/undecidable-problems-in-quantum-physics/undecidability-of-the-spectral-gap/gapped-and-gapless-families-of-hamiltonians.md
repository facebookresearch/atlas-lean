# Gapped and gapless families of lattice Hamiltonians

A family of lattice Hamiltonians indexed by system size is gapped when, for all large sizes, its lowest eigenvalue is simple and separated from the rest of the spectrum by a fixed amount, and gapless when the spectrum fills a fixed interval above the ground-state energy densely as the size grows.

Let $\{H^{\Lambda(L)}\}_{L\in\mathbb N}$ be a family of [translation-invariant lattice Hamiltonians](translation-invariant-lattice-hamiltonians.md), with eigenvalues $\lambda_0\le\lambda_1\le\cdots$ and spectral gap $\Delta(H^{\Lambda(L)})=\lambda_1-\lambda_0$.

- The family is *gapped* if there are a constant $\gamma>0$ and a size $L_0$ such that for all $L>L_0$ the eigenvalue $\lambda_0(H^{\Lambda(L)})$ is non-degenerate and $\Delta(H^{\Lambda(L)})\ge\gamma$; one then says that the spectral gap is at least $\gamma$.
- The family is *gapless* if there is a constant $c>0$ such that for every $\varepsilon>0$ there is an $L_0$ for which, for all $L>L_0$, every point of $[\lambda_0(H^{\Lambda(L)}),\lambda_0(H^{\Lambda(L)})+c]$ lies within distance $\varepsilon$ of the spectrum of $H^{\Lambda(L)}$.

Gapped is not the negation of gapless: a family whose gap closes without the spectrum becoming dense, or whose ground state stays degenerate, is neither. The strong definitions avoid such ambiguous cases, and the undecidability results for the spectral gap use families guaranteed to fall into one of the two classes. The same definitions are used for chains, indexed by the chain length, and for families with plaquette interactions.

## Depends on

- [Translation-invariant nearest-neighbor lattice Hamiltonians](translation-invariant-lattice-hamiltonians.md)

## Proof depends on

None.

## Sources

- T. Cubitt, D. Perez-Garcia and M. M. Wolf, "Undecidability of the spectral gap", *Forum of Mathematics, Pi* 10, e14, 2022, doi:[10.1017/fmp.2021.15](https://doi.org/10.1017/fmp.2021.15); read in arXiv:1502.04573v5 ([arXiv](https://arxiv.org/abs/1502.04573v5)), whose numbering is used: Definitions 1 (gapped) and 2 (gapless) and the remark after them.
