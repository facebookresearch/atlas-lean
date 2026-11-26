# Poisson clicktimes of the tournament ratchet

The *tournament ratchet* is a model of Muller's ratchet with pairwise selection. For parameters $N$, $m_N$, $s_N>0$ it is the Markov jump process $\mathfrak N^{(N)}=(\mathfrak N_\kappa^{(N)}(t))_{\kappa\ge0}$ on $\{(n_0,n_1,\dots)\in\mathbb N_0^{\mathbb N_0}:\sum_\kappa n_\kappa=N\}$, where $\mathfrak N_\kappa$ is the number of individuals carrying $\kappa$ deleterious mutations, with transitions

- neutral reproduction: for $\kappa\ne\kappa'$, $(\mathfrak N_\kappa,\mathfrak N_{\kappa'})\to(\mathfrak N_\kappa+1,\mathfrak N_{\kappa'}-1)$ at rate $\tfrac1{2N}\mathfrak N_\kappa\mathfrak N_{\kappa'}$;
- selective reproduction: for $\kappa<\kappa'$, the same jump at rate $\tfrac{s_N}N\mathfrak N_\kappa\mathfrak N_{\kappa'}$;
- mutation: $(\mathfrak N_\kappa,\mathfrak N_{\kappa+1})\to(\mathfrak N_\kappa-1,\mathfrak N_{\kappa+1}+1)$ at rate $m_N\mathfrak N_\kappa$.

Let $K_N^\star(t)=\min\{\kappa:\mathfrak N_\kappa(t)>0\}$ be the type of the fittest class and $\mathcal T_N^{(i)}=\inf\{t:K_N^\star(t)=i\}$ the $i$-th *clicktime* of the ratchet. While the fittest class is $\kappa$, its size evolves autonomously as the two-type Moran chain $Y_0^{(N)}$ of the [metastability node](metastability-of-the-two-type-moran-model-with-one-way-mutation.md).

**Theorem.** Assume $1/N\ll m_N<s_N\ll1$, $m_N/s_N\to\rho^*\in(0,1]$, and the exponential regime $Nm_N(1-m_N/s_N)^2\to\infty$, and start with $\mathfrak N_0^{(N)}(0)\gg\mathfrak c_N=1/(s_N-m_N)$. With $e_N$ the asymptotic mean extinction time of the metastability node, the processes $(K_N^\star(e_Nt))_{t\ge0}$ converge in distribution to a rate-$1$ Poisson counting process. Equivalently, the rescaled clicktimes $(\mathcal T_N^{(i)}/e_N)_{i\ge1}$ converge to a rate-$1$ Poisson point process on $\mathbb R_+$.

So in the exponential regime the ratchet clicks at exponentially long, asymptotically memoryless intervals of mean $e_N$. Every finite ratchet with positive mutation clicks infinitely often, as in [almost-sure repeated clicking of a finite mutation ratchet](muller-s-ratchet-model-and-almost-sure-clicking.md); this theorem identifies the law of the clicktimes.

## Depends on

- [Metastability of the two-type Moran model with one-way mutation](metastability-of-the-two-type-moran-model-with-one-way-mutation.md)
- [Almost-sure repeated clicking of a finite mutation ratchet](muller-s-ratchet-model-and-almost-sure-clicking.md)

## Expansion

Each click is the extinction of the current fittest class, which by the metastability theorem happens after an asymptotically exponential time of mean $e_N$ when the class starts above the critical size. The remaining step shows that at each click the next class already has size $\gg\mathfrak c_N$ with high probability (because many mutations flow out of the dying class during its final descent), so the next inter-click time is again asymptotically exponential with mean $e_N$ and asymptotically independent of the past. Iterating gives the Poisson limit.

## Sources

- J. L. Igelbrink, C. Smadi and A. Wakolbinger, "The tournament ratchet's clicktime process, and metastability in a Moran model", arXiv preprint (2025), <https://doi.org/10.48550/arXiv.2512.24779>. Definition 2.1, Remark 2.2, Theorem 2.3, Theorem 2.4(d)-(e), and Section 4 (proof of Theorem 2.3, including Proposition 4.1).
