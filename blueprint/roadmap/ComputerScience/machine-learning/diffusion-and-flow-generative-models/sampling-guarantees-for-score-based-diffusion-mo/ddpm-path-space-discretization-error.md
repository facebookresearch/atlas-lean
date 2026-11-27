# Path-space discretization error for DDPM

This node collects the discretization estimate behind the DDPM sampling guarantee of Chen et al. Under the assumptions of that guarantee (a finite moment of order $2 + \eta$ of the data distribution $q$ for some $\eta > 0$, with $m_2^2 = \mathbb{E}_q[\|x\|^2]$; $L$-Lipschitz scores $\nabla \ln q_t$ of the forward marginals for every $t \ge 0$, with $L \ge 1$; and score estimates with $\mathbb{E}_{q_{kh}}[\|s_{kh} - \nabla \ln q_{kh}\|^2] \le \varepsilon^2$ for $k = 1, \dots, N$, where $\varepsilon \ge 0$), let $Q^{\leftarrow}_T$ be the law on path space of the time reversal on $[0, T]$ of the forward Ornstein–Uhlenbeck process started from $q$, and let $P^{q_T}_T$ be the law on path space of the sampler run in continuous time from $q_T$, with the score estimate frozen at the start of each step. If $h = T/N \lesssim 1/L$, then

$$
\mathrm{TV}(P^{q_T}_T, Q^{\leftarrow}_T)^2 \le \mathrm{KL}(Q^{\leftarrow}_T \,\|\, P^{q_T}_T) \lesssim \bigl(\varepsilon^2 + L^2 d h + L^2 m_2^2 h^2\bigr)\, T .
$$

## Depends on

- [Forward Ornstein–Uhlenbeck marginal](ou-marginal.md)
- [Score of a density](log-density-score.md)
- [DDPM sampler step](ddpm-step.md)
- [Total variation distance between finite measures](../../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Proof depends on

- [Girsanov's theorem for bounded progressive drift](../../../../Probability/stochastic-calculus/it-s-formula/girsanov-change-of-measure-for-bounded-drift.md)
- [Optional stopping theorem in continuous time](../../../../Probability/martingales/optional-stopping-theorem/stopped-value-ae-eq-cond-exp-of-le-of-co.md)
- [Data-processing inequality for the Kullback–Leibler divergence](../../../../InformationTheory/information-inequalities/data-processing-inequality/kl-div-map-le.md)
- [Lower semicontinuity of the Kullback–Leibler divergence](../../../../InformationTheory/information-inequalities/donsker-varadhan-variational-formula/lower-semicontinuity-of-the-kl-divergence.md)
- [Pinsker's inequality, square-root form](../../../../InformationTheory/information-inequalities/total-variation-and-pinsker-s-inequality/total-variation-dist-le-sqrt-kl-div.md)

## Expansion

A sound expansion has separate pages for:

1. **The two path laws.** The time reversal of the forward process on $[0, T]$, which solves $dX_t = \{X_t + 2\,\nabla \ln q_{T-t}(X_t)\}\,dt + \sqrt2\,dB_t$ with $X_0 \sim q_T$, and the continuous-time sampler $dX_t = \{X_t + 2\, s_{T-kh}(X_{kh})\}\,dt + \sqrt2\,dB_t$ on $[kh, (k+1)h]$ with $X_0 \sim q_T$, whose law after each step of length $h$ from a point is a step of the discrete sampler.
2. **Moment and movement bounds** along the forward process $(\bar X_t)$: $\mathbb{E}[\|\bar X_t\|^2] \le d \vee m_2^2$ and $\mathbb{E}[\|\nabla \ln q_t(\bar X_t)\|^2] \le L d$ for $t \ge 0$, and $\mathbb{E}[\|\bar X_t - \bar X_s\|^2] \lesssim \delta^2 m_2^2 + \delta d$ for $0 \le s < t$ with $\delta = t - s \le 1$.
3. **The score perturbation bound** that controls $\nabla \ln (q_{T-kh}/q_{T-t})$ over one step.
4. **The change of measure** for the adapted drift $b_t = \sqrt2\,\{s_{T-kh}(X_{kh}) - \nabla \ln q_{T-t}(X_t)\}$ on $[kh, (k+1)h]$, with $\mathbb{E}\int_0^T \|b_t\|^2\,dt < \infty$ under $Q^{\leftarrow}_T$.
   - It needs Girsanov's theorem for a $d$-dimensional Brownian motion $B$ and an $\mathbb{R}^d$-valued progressively measurable drift with $\mathbb{E}\int_0^T \|b_t\|^2\,dt < \infty$, under the condition $\mathbb{E}\,\mathcal{E}(L)_T = 1$ for $L_t = \int_0^t \langle b_s, dB_s \rangle$ (the source's Theorem 9). The linked Girsanov theorem is only its case $d = 1$ with a bounded drift, and applying it to each coordinate does not give the joint law of a $d$-dimensional Brownian motion, so the expansion proves the vector statement.
   - Novikov's condition need not hold, so the bound is first proved for the laws $P^n$ of the process that runs the sampler up to the stopping time $T_n = \inf\{t : \int_0^t \|b_s\|^2\,ds \ge n\} \wedge T$ and the reverse process after it, using $\mathbb{E}\, L_{T_n} = 0$ by optional stopping.
   - For the truncations $\pi_\varepsilon(\omega)(t) = \omega(t \wedge (T - \varepsilon))$ on $C([0, T]; \mathbb{R}^d)$, $\pi_\varepsilon$ pushes $P^n$ forward to laws converging weakly to $\pi_{\varepsilon\#} P^{q_T}_T$. Lower semicontinuity and the data-processing inequality for the KL divergence give $\mathrm{KL}(\pi_{\varepsilon\#} Q^{\leftarrow}_T \,\|\, \pi_{\varepsilon\#} P^{q_T}_T) \le \liminf_n \mathrm{KL}(Q^{\leftarrow}_T \,\|\, P^n)$, and lower semicontinuity again, as $\varepsilon \to 0$, gives the bound for $Q^{\leftarrow}_T$ and $P^{q_T}_T$.

## Sources

- S. Chen, S. Chewi, J. Li, Y. Li, A. Salim and A. R. Zhang, *Sampling is as easy as learning the score: theory for diffusion models with minimal data assumptions*, ICLR 2023, Appendix B: Theorem 10 and its proof (B.1–B.2), Lemmas 11 and 12 (B.4), and the score perturbation lemma, Lemma 17 (C.4). <https://par.nsf.gov/servlets/purl/10502932>
