# Weak eigenvector localization and segregated cortical timescales

**Definitions.** Let $\delta$ be a small parameter and $e_k$ the $k$-th standard basis vector.

- A vector $u(\delta)$ is *weakly localized* if $u = a e_k + \delta b + O(\delta^2)$ for some $k$, a nonzero constant $a$ and a constant vector $b$.
- Vectors $u(\delta), v(\delta)$ are *weakly orthogonal* if $\langle u, v\rangle = O(\delta)$.

**Setting.** In the linearised multiareal excitatory–inhibitory model $\dot\nu = W\nu + I_{\mathrm{ext}}$, transform by the matrix $P$ that diagonalises the local block (see the local scale-separation result), giving $P^{-1}WP = \Lambda + \Sigma$ with

$$\Sigma = \begin{pmatrix}\Sigma_{UL} & \Sigma_{UR}\\ \Sigma_{LL} & \Sigma_{LR}\end{pmatrix}.$$

The second small parameter is the *detailed excitation–inhibition balance* of each long-range pathway,

$$\delta = \frac{\mu_{EE}}{\mu_{IE}} - \frac{w_{EI}}{w_{II} + 1/\beta_I},$$

which makes the long-range input to an area's excitatory population nearly cancelled by the local inhibition it recruits. Then $\Sigma_{UL} = O(\epsilon(\delta + \epsilon))$, $\Sigma_{UR} = O(\epsilon^2(\delta + \epsilon))$ (dropped, with eigen-error of the same order), the $O(\epsilon^2)$ parts coming from the remainder of $A$ (the source states $O(\epsilon\delta)$ and $O(\epsilon^2\delta)$, which need $\epsilon = O(\delta)$), $\Sigma_{LL} = O(1)$, $\Sigma_{LR} = O(\epsilon)$, and an eigenvector $(u,v)$ with eigenvalue $\lambda$ satisfies

$$(\Lambda_U + \Sigma_{UL})u = \lambda u,\qquad \Sigma_{LL}u + (\Lambda_L + \Sigma_{LR})v = \lambda v.$$

**Proposition.** If all matrices are analytic in $\epsilon,\delta$, the orders above hold with $\epsilon = O(\delta)$ (so $\Sigma_{UL} = O(\epsilon\delta)$ and $\Sigma_{UR} = O(\epsilon^2\delta)$, as in the source), $\Lambda_U = O(\epsilon)$, $\Lambda_L = O(1)$, $\Lambda_U/\epsilon$ has $n$ simple eigenvalues at $\epsilon = 0$ (gaps $\lvert(\Lambda_U)_{jj} - (\Lambda_U)_{kk}\rvert \ge c\epsilon$), and $\Lambda_L + \Sigma_{LR}$ is diagonalizable, then

1. there are $n$ eigenvectors with $u = 0$ and $\lambda = O(1)$;
2. there are $n$ eigenvectors with $u$ weakly localized and pairwise weakly orthogonal and $\lambda = O(\epsilon)$.

Mapping back, the unit eigenvectors $(r_E, r_I)$ of $W$ satisfy: for $\lambda = O(\epsilon)$, $r_E = c^{-1}(I + AB)e_k + O(\epsilon) + O(\delta)$, i.e. the excitatory parts are localized and orthogonal up to $O(\epsilon + \delta)$; for $\lambda = O(1)$, $r_E = O(\epsilon)$. Hence each area's excitatory population sees essentially one slow timescale of its own, and fast modes are invisible in excitatory activity.

**First-order correction and the spectral gap.** Under the same hypotheses (in particular $\epsilon = O(\delta)$, so that $\bar\Sigma_{UL}$ below is bounded), writing $\bar\Lambda_U = \Lambda_U/\epsilon$ (diagonal entries $\bar\lambda_j$), $\bar\Sigma_{UL} = \Sigma_{UL}/(\epsilon\delta)$ and $u = e_k + \delta u_1 + O(\delta^2)$,

$$u_{1,j} = \frac{(\bar\Sigma_{UL})_{jk}}{\bar\lambda_k - \bar\lambda_j}\qquad (j \neq k).$$

Localization survives as long as long-range coupling is small relative to the spectral gaps $\bar\lambda_k - \bar\lambda_j$, which a macroscopic gradient of local excitation across the hierarchy supplies.

## Expansion

Item 1 follows because $u = 0$ solves the first equation, leaving $v$ an eigenvector of $\Lambda_L + \Sigma_{LR}$. For item 2, divide by $\epsilon$: $u$ is an eigenvector of $\bar\Lambda_U + \delta\bar\Sigma_{UL}$, a diagonal matrix with simple spectrum perturbed analytically, so $u$ and $\lambda/\epsilon$ have convergent power series in $\delta$ whose zeroth-order eigenvectors are the $e_k$. The three biological requirements are therefore: distinct excitatory and inhibitory physiology (small $\epsilon$), detailed balance of long-range excitation with local inhibition (small $\delta$), and a gradient of excitation (spectral gaps), the last acting like disorder-induced (Anderson-type) localization.

## Depends on

- [Scale separation of local excitatory–inhibitory eigenvalues](scale-separation-of-local-excitatory-inhibitory-eigenvalues.md)

## Sources

- S. Li, X.-J. Wang, *Hierarchical timescales in the neocortex: Mathematical mechanism and biological insights*, Proc. Natl. Acad. Sci. USA 119 (2022), e2110274119, Eqs. 6–11, Definitions 1–2 and Propositions 2–3; SI Appendix, Proposition S1 (error from dropping $\Sigma_{UR}$). <https://doi.org/10.1073/pnas.2110274119> (PMCID: PMC8832993)
