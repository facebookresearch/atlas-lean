# Which fixed point a renormalization group flow reaches is undecidable

For the Hamiltonians with undecidable spectral gap there is a real-space renormalization group map, computable at every step and preserving gapped and gapless behavior, under which each Hamiltonian flows to one of two fixed points; which one cannot be decided.

Let $h(\varphi)$, $\varphi\in\mathbb Q$, be the local interaction of the [two-dimensional Hamiltonians with undecidable spectral gap](the-spectral-gap-of-two-dimensional-hamiltonians.md), and $H(\varphi)=\sum h(\varphi)^{(i,j)}$; $H(\varphi)$ is [gapped](gapped-and-gapless-families-of-hamiltonians.md) if the universal Turing machine encoded in $h(\varphi)$ halts on input $\varphi$ and gapless if it never halts.

**Theorem (Watson, Onorati and Cubitt).** There is a real-space renormalization group map $\mathcal R$ acting on such Hamiltonians, with $k$-fold iterate $\mathcal R^{(k)}$, such that:

1. $\mathcal R$ is computable;
2. $\mathcal R^{(k)}(H(\varphi))$ is gapped if $H(\varphi)$ is gapped and gapless if $H(\varphi)$ is gapless, and the order parameter distinguishing the two phases has a renormalized counterpart that still distinguishes them;
3. for every $k$, the renormalized local interactions $\mathcal R^{(k)}(h(\varphi))$ lie in an explicit family $\mathcal F(\varphi,\tau_1,\tau_2,\{\alpha_i\},\{\beta_i\})$ whose parameters at step $k$ are computable;
4. if the universal machine does not halt on input $\varphi$, then $\tau_2(k)=-2^k$ for all $k>k_0(\varphi)$, with $k_0(\varphi)$ computable; if it halts, there is an uncomputable $k_h(\varphi)$ with $\tau_2(k)=-2^k$ for $k_0(\varphi)<k<k_h(\varphi)$ and $\tau_2(k)=-2^k+\Omega(4^{k-k_h(\varphi)})$ for all $k>k_h(\varphi)$.

The Hamiltonian flows to one of two fixed points, a gapped one with low-energy properties like an Ising model in a field and a gapless one like the critical XY model, and determining which fixed point $H(\varphi)$ flows to under $\mathcal R$ is undecidable (Corollary 10).

Each individual step of the flow is computable; what cannot be computed is its long-run behavior, including the step $k_h(\varphi)$ at which the trajectory leaves the non-halting branch.

## Depends on

- [The spectral gap of two-dimensional translation-invariant Hamiltonians is undecidable](the-spectral-gap-of-two-dimensional-hamiltonians.md)
- [Gapped and gapless families of lattice Hamiltonians](gapped-and-gapless-families-of-hamiltonians.md)
- [Halting of a code on an input](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/halts.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The renormalization map combines a renormalization of the classical Robinson tiling part, which maps the tiling to a coarser copy of itself by grouping blocks of tiles, with a renormalization of the quantum part that keeps track of the history-state computations placed along the tiling segments; exact formulas for the renormalized interactions keep them in the family $\mathcal F$. Since $\mathcal R$ preserves gapped and gapless behavior and the gapped and gapless cases flow to different fixed points, deciding the fixed point would decide the spectral gap of $H(\varphi)$, which is undecidable. The divergence statement follows by tracking, through the explicit renormalized family, the coefficient $\tau_2$ of the projector term in the renormalized on-site interaction; in the halting case its departure from $-2^k$ starts at a step $k_h(\varphi)$ tied to the halting computation, which cannot be computed. A good expansion links pages for the Robinson tiling and its block renormalization and for the structure of the history-state Hamiltonian under renormalization; neither has a page yet.

## Sources

- J. D. Watson, E. Onorati and T. S. Cubitt, "Uncomputably complex renormalisation group flows", *Nature Communications* 13, 7618, 2022, doi:[10.1038/s41467-022-35179-4](https://doi.org/10.1038/s41467-022-35179-4); read in arXiv:2102.05145v1 ([arXiv](https://arxiv.org/abs/2102.05145v1)), whose numbering is used: Theorem 1 (informal statement), Theorems 8 and 9, Corollary 10, Definitions 2 and 3 (gapped and gapless) and Theorem 13 (renormalization of the Robinson tiling Hamiltonian).
- T. Cubitt, D. Perez-Garcia and M. M. Wolf, "Undecidability of the spectral gap", *Forum of Mathematics, Pi* 10, e14, 2022, doi:[10.1017/fmp.2021.15](https://doi.org/10.1017/fmp.2021.15): the Hamiltonian $H(\varphi)$ being renormalized.
