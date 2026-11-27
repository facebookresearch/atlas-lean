# Early-stopped sampling guarantees for compactly supported data

This node collects the guarantees of Chen et al. for score-based diffusion sampling from a data distribution $q$ supported on a ball, which assume no density, no Lipschitz score and no finite KL divergence from the standard Gaussian: the DDPM sampler is stopped early.

## Depends on

- [Forward Ornstein–Uhlenbeck marginal](ou-marginal.md)
- [Score of a density](log-density-score.md)
- [DDPM sampler laws](ddpm-law.md)
- [Wasserstein distance of order $p$](../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein.md)
- [Total variation distance between finite measures](../../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Proof depends on

- [Sampling guarantee for score-based diffusion (DDPM)](tv-dist-ddpm-output-le.md)
- [Data-processing inequality for total variation](../../../../InformationTheory/information-inequalities/strong-data-processing-and-dobrushin-s-coefficie/total-variation-dist-comp-le-self.md)
- [Triangle inequality for the Wasserstein distance](../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein-triangle.md)
- [Monotonicity of the Wasserstein distances in the exponent](../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein-mono.md)
- [Kantorovich–Rubinstein bound for real Lipschitz functions](../../../../MeasureTheory/optimal-transport/wasserstein-distances/kantorovich-rubinstein-formula/enorm-integral-sub-le-mul-wasserstein-on.md)
- [Wasserstein distance as an infimum over couplings](../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein-eq-i-inf.md)
- [Every coupling bounds the Wasserstein distance](../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein-le-of-is-coupling.md)
- [Wasserstein distance controlled by total variation](../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance-and-total-variation/wasserstein-one-le-mul-total-variation-d.md)

## Expansion

A sound expansion has separate pages for:

1. **Early-stopped target** (Lemma 3, Lemma 21 of the supplement). If $q$ is supported on the ball of radius $R \ge 1$ and $0 < \varepsilon_{W_2} \ll \sqrt d$, the forward marginal $q_t$ at a time $t \asymp \varepsilon_{W_2}^2/(\sqrt d\,(R \vee \sqrt d))$ satisfies $W_2(q_t, q) \le \varepsilon_{W_2}$ and $\mathrm{KL}(q_t \Vert \gamma^d) \lesssim \sqrt d\,(R \vee \sqrt d)^3/\varepsilon_{W_2}^2$, and for every $t' \ge t$ the score of $q_{t'}$ is $L$-Lipschitz with $L \lesssim d R^2 (R \vee \sqrt d)^2/\varepsilon_{W_2}^4$.
2. **Guarantees** (Corollaries 4–6). The stopping time is on the sampler's grid: $T = N h$ and $t = m h$ with $0 \le m < N$, and the output $p_{T-t}$ is the law after $N - m$ steps started at the standard Gaussian, which uses the estimates $s_{kh}$ for $k = m + 1, \dots, N$. The score error is $\varepsilon_{\mathrm{score}} \ge 0$ with $\mathbb{E}_{q_{kh}}[\|s_{kh} - \nabla \ln q_{kh}\|^2] \le \varepsilon_{\mathrm{score}}^2$ for those $k$, and $h$ is chosen as in the DDPM guarantee applied to the target $q_t$.
   - **Total variation** (Corollary 4): $p_{T-t}$ is $\varepsilon_{\mathrm{TV}}$-close to $q_t$ in total variation when $N = \widetilde\Theta(d^3 R^4 (R \vee \sqrt d)^4/(\varepsilon_{\mathrm{TV}}^2 \varepsilon_{W_2}^8))$ and $\varepsilon_{\mathrm{score}} \le \widetilde O(\varepsilon_{\mathrm{TV}})$.
   - **Bounded Lipschitz metric** (Corollary 5), $d_{\mathrm{BL}}(\mu, \nu) = \sup\{\int f\,d\mu - \int f\,d\nu : f\colon \mathbb{R}^d \to [-1, 1] \text{ is 1-Lipschitz}\}$: with $\varepsilon_{W_2}$ and $\varepsilon_{\mathrm{TV}}$ of order $\varepsilon$, $d_{\mathrm{BL}}(p_{T-t}, q) \le \varepsilon$ when $N = \widetilde\Theta(d^3 R^4 (R \vee \sqrt d)^4/\varepsilon^{10})$ and $\varepsilon_{\mathrm{score}} \le \widetilde O(\varepsilon)$.
   - **$W_2$ after projection** (Corollary 6, proved in Appendix B.5): with $\varepsilon_{W_2} = \varepsilon/3$ and $\varepsilon_{\mathrm{TV}} = \widetilde\Theta(\varepsilon^2/R^2)$, the output projected onto the ball of radius $R_0 = \widetilde\Theta(R)$ is $\varepsilon$-close to $q$ in $W_2$ when $N = \widetilde\Theta(d^3 R^8 (R \vee \sqrt d)^4/\varepsilon^{12})$ and $\varepsilon_{\mathrm{score}} \le \widetilde O(\varepsilon^2/R^2)$.
3. **Comparisons of distances** that the corollaries use beyond the linked pages:
   - $|\int f\,d\mu - \int f\,d\nu| \le 2\, \mathrm{TV}(\mu, \nu)$ for measurable $f\colon \mathbb{R}^d \to [-1, 1]$, so $d_{\mathrm{BL}} \le 2\, \mathrm{TV}$, while $d_{\mathrm{BL}} \le W_1 \le W_2$ (Corollary 5);
   - $W_2(\phi_\# \mu, \phi_\# \nu) \le W_2(\mu, \nu)$ for a 1-Lipschitz map $\phi$, such as the projection onto a ball, by pushing couplings forward;
   - $W_2(\mu, \nu)^2 \le 2R_0\, W_1(\mu, \nu) \le 4R_0^2\, \mathrm{TV}(\mu, \nu)$ for laws supported on the ball of radius $R_0$. This is a derived bound of the form the source takes from Rolland (2022, Lemma 9) in Appendix B.5, without that lemma's extra term $R_0 e^{-R_0}$.

## Sources

- S. Chen, S. Chewi, J. Li, Y. Li, A. Salim and A. R. Zhang, *Sampling is as easy as learning the score: theory for diffusion models with minimal data assumptions*, ICLR 2023, Section 3.2: Lemma 3 (Lemma 21 of the supplement) and Corollaries 4–6, with the proof of Corollary 6 in Appendix B.5. <https://par.nsf.gov/servlets/purl/10502932> In arXiv:2209.11215v3 they are Lemma 20 and Corollaries 3–5.
