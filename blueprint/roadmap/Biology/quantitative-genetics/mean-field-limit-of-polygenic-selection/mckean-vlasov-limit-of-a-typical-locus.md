# McKean–Vlasov limit of a typical locus under strong recombination

**Model.** A haploid population with $L$ biallelic loci, alleles coded $\gamma^\ell \in \{-1, +1\}$, evolves by a multilocus Wright–Fisher diffusion with mutation rates $\theta^{(+)}, \theta^{(-)}$ towards $+1$ and $-1$, recombination measure $\rho\nu$ on subsets of $[L]$, and log-fitness $W(\gamma) = U(Z(\gamma))$ of the additive trait $Z(\gamma) = \frac{1}{L}\sum_\ell \gamma^\ell$, where $U$ is a polynomial of degree at most 2 (for instance $U(z) = -\kappa(z - z^*)^2$; $\kappa > 0$ stabilizing, $\kappa < 0$ disruptive). Let $p^\ell(\mathbf X_t)$ be the frequency of $+1$ at locus $\ell$ and $\mu_{\mathbf X_t} = \frac1L \sum_\ell \delta_{p^\ell(\mathbf X_t)}$. With $r_{\{\ell_1,\ell_2\}}$ the pairwise recombination rate, define the harmonic means $1/r^*_{\ell_0} = \frac{1}{L-1}\sum_{\ell \ne \ell_0} 1/r_{\{\ell_0,\ell\}}$ and $1/r^{**} = \frac1L \sum_{\ell_0} 1/r^*_{\ell_0}$.

**Theorem.** Suppose $\mu_{\mathbf X_0}$ converges in law to a deterministic $m_0$ and $\rho r^{**} \gg L^2 \ln \rho$. Then for every $T > 0$, $(\mu_{\mathbf X_t})_{t \le T}$ converges weakly in Skorokhod space to $(\mathcal L(f_t))_{t \le T}$, where $f$ is the unique weak solution of the McKean–Vlasov equation
$$df_t = \bar s(\mathcal L(f_t))\, f_t(1 - f_t)\, dt + \bar\Theta(f_t)\, dt + \sqrt{f_t(1 - f_t)}\, dB_t, \qquad \mathcal L(f_0) = m_0,$$
with $\bar s(\zeta) = 2U'(\langle \zeta, 2\,\mathrm{Id} - 1\rangle)$ and $\bar\Theta(x) = \theta^{(+)}(1-x) - \theta^{(-)}x$; equivalently $\mathcal L(f_t)$ is the unique weak solution of the nonlinear Fokker–Planck equation
$$\partial_t u_t = -\partial_x\bigl[(\bar s(u_t)\, x(1-x) + \bar\Theta(x))\, u_t\bigr] + \tfrac12 \partial_{xx}\bigl(x(1-x) u_t\bigr).$$
If finitely many tagged loci have pairwise recombination $\rho r_{\{\ell_i,\ell_j\}} \gg L$ (and $\rho r^*_{\ell_i} \gg L^2 \ln \rho$) and start from $m_0^{\otimes n}$, their frequencies converge to $n$ independent copies of $f$. Moreover, with $\varepsilon_L = (\rho r^{**})^{-1/2}$,
$$\mathbb E\Bigl[\sup_{t \in [\varepsilon_L, T]} \bigl| L\,\mathrm{Var}_{\mathbf X_t}[Z] - 4\,\mathbb E[f_t(1 - f_t)] \bigr|\Bigr] \to 0 .$$

## Depends on

- [The infinitesimal model of inheritance](../mendelian-segregation-and-the-infinitesimal-mode/infinitesimal-model-definition.md)

## Expansion

Strong recombination keeps the population near linkage equilibrium, so pairwise and triple linkage disequilibria are $O(1/(\rho r))$ and the selection gradient felt by one locus reduces to $U'$ evaluated at the mean trait. Because each locus contributes $1/L$ to $Z$, the mean trait is a law of large numbers over loci, which is approximated by the law of the focal locus itself: propagation of chaos. Selection therefore percolates from the trait to each locus as a frequency-independent but law-dependent coefficient, giving a nonlinear Wright–Fisher diffusion, and the additive genetic variance follows from independence of loci.

## Sources

- P. Courau, A. Lambert, E. Schertzer, "The gene's-eye view of quantitative genetics", arXiv:2502.12831 (2025), Theorems 1.1 and 1.3 and Corollary 2.3, <https://doi.org/10.48550/arXiv.2502.12831>.
