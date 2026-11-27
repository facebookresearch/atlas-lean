# Spectral estimation of grade-of-membership admixture models under local dependence

**Generalized grade-of-membership (GoM) model.** $N$ subjects (individuals) each have a membership vector $\pi_i^*\in\Delta_{K-1}=\{x\in\mathbb{R}^K_{\ge0}:\sum_kx_k=1\}$ over $K$ extreme profiles (ancestral populations). The observed $N\times J$ data matrix is

$$R=R^*+E,\qquad R^*=\mathbb{E}[R]=\Pi^*\Theta^{*\top},\qquad \Pi^*\in[0,1]^{N\times K},\ \Theta^*\in\mathbb{R}^{J\times K}.$$

Examples are flattened categorical survey responses (one-hot columns per item), genotype counts with $R_{ij}\sim\mathrm{Binom}(2,\sum_k\pi^*_{ik}\theta^*_{jk})$ as in the STRUCTURE/ADMIXTURE admixture model (where $R^*=2\Pi^*\Theta^{*\top}$), and Poisson single-cell counts.

**Assumptions.**
- *Block-dependent noise.* The columns split into blocks $S_1,\dots,S_L$ of size at most $M$. The noise vectors $E_{i,S_l}$ are independent across subjects $i$ and blocks $l$, with arbitrary dependence inside a block (for example, linkage disequilibrium among neighboring SNPs). Entries are bounded by $B$ with high probability.
- *Pure subjects.* Every profile has at least one pure subject ($\pi_i^*=e_k$), and $\mathrm{rank}(\Theta^*)=K$.

**Identifiability (Lemma 1).** Let $R^*=U^*\Lambda^*V^{*\top}$ be the rank-$K$ SVD and $\mathcal{S}$ the indices of one pure subject per profile. Then the model is identifiable up to permutation of profiles, and

$$\Pi^*=U^*(U^*_{\mathcal{S},:})^{-1},\qquad \Theta^*=V^*\Lambda^*U^{*\top}_{\mathcal{S},:}.$$

So the rows of $U^*$ lie in a simplex whose vertices are the pure subjects, and each subject's weights are its membership scores.

**Estimator.** Compute the top-$K$ SVD $R\approx U\Lambda V^\top$. Find vertex indices $\hat{\mathcal{S}}$ by successive projection on the rows of $U$: repeatedly take the row of largest norm and project out its direction. Set $\hat\Pi=U(U_{\hat{\mathcal{S}},:})^{-1}$ and $\hat\Theta=V\Lambda U^\top_{\hat{\mathcal{S}},:}$, then truncate and renormalize to valid ranges.

**Theorem (uniform consistency).** Write $\sigma^2=\max_{i,j}\mathrm{Var}(E_{ij})$, $\tilde\sigma^2=\max_{i,l}\|\mathrm{Cov}(E_{i,S_l})\|$, $\kappa^*=\sigma_1^*/\sigma_K^*$, and let $\mu_1,\mu_2$ be the incoherence parameters of $U^*,V^*$. Assume $K\ll\min\{N,L\}$, $ML\asymp J$, a signal-strength condition $\sigma_K(\Pi^*)\sigma_K(\Theta^*)\gtrsim\sigma\kappa^*(M\sqrt N+\sqrt J)$, and an incoherence condition. Then, with probability $1-O((N\vee J)^{-10})$ and up to a permutation $P$ of profiles,

$$\|\hat\Pi-\Pi^*P\|_{2,\infty}=O\big(\kappa^2(\Pi^*)\sigma_1(\Pi^*)\,\xi_1\big),\qquad \|\hat\Theta-\Theta^*P\|_\infty=O\big(\kappa^2(\Pi^*)\,\xi_3\big).$$

Here $\xi_1$ and $\xi_3$ are the two-to-infinity and entrywise singular-subspace perturbation bounds for block-dependent noise. In simplified form,

$$\xi_1\asymp\Big(\frac{\tilde\sigma\sqrt{N\log(N\vee J)}}{\sigma_K^*}+\frac{\kappa^*\sigma^2J}{\sigma_K^{*2}}\Big)\sqrt{\frac{\mu_1K}{N}},\qquad \xi_3\asymp\kappa^*K\sigma\sqrt{\mu_1\mu_2}\,\log(N\vee J)\sqrt{\frac{M}{J}+\frac1N}.$$

The dependence of these bounds on the block size $M$ is sharp, and $\xi_3$ matches the minimax rate up to a logarithm.

**Corollary (Dirichlet memberships).** Suppose $\pi_i^*\sim\mathrm{Dir}(\alpha)$ and the item blocks are $\mathrm{Dir}(\beta)$ with balanced, bounded parameters, and $N,J$ are large enough. Then, with probability $1-O(K(N\wedge L)^{-3})$,

$$\|\hat\Pi-\Pi^*P\|_{2,\infty}\lesssim\frac{M^{3/2}K^{5/2}\sqrt{\log(N\vee J)}}{\sqrt J}+\frac{MK^{9/4}}{N}.$$

## Depends on

- [Admixture model and the FRAPPE EM algorithm](../README.md)

## Expansion

Membership scores are convex weights, so $U^*=\Pi^*U^*_{\mathcal{S},:}$. The left singular vectors therefore form a $K$-vertex simplex cloud, and recovering memberships reduces to finding its vertices, which successive projection does stably. The analysis has two parts. The first is a leave-one-block-out perturbation bound for asymmetric low-rank matrices with locally dependent noise. It treats $U$ and $V$ separately, so that very unbalanced shapes ($N\ll J$ for SNP data) and incoherences ($\mu_1\ll\mu_2$) are not lost through symmetric dilation. The second uses matrix concentration universality to obtain $\|E\|\lesssim\tilde\sigma\sqrt N+\sigma\sqrt J$ without an extra $\sqrt{\log}$ factor. Applied to HapMap3 genotypes of four populations ($N=467$, $J=274{,}128$), the estimator places ASW individuals as an admixture of YRI-like and CEU-like ancestry and MEX individuals between CEU and a third ancestral component. It does so in seconds, without MCMC.

## Sources

- Ling Chen, Chengzhu Huang and Yuqi Gu, "Generalized Grade-of-Membership Estimation for High-Dimensional Locally Dependent Data", J. Amer. Statist. Assoc. (2026), online first, <https://doi.org/10.1080/01621459.2026.2670011>. Numbering follows the arXiv version, arXiv:2412.19796 (2024): Assumptions 1–4, Lemma 1, Theorem 1 (two-to-infinity singular subspace perturbation under local dependence), Remark 1, Theorem 2 (uniform consistency), Corollaries 1 and 2, and Algorithm 1, with the HapMap3 application in Section 6, <https://doi.org/10.48550/arXiv.2412.19796>.
