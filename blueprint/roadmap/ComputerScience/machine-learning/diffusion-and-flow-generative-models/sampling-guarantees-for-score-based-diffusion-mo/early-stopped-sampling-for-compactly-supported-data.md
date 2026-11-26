# Early-stopped sampling guarantees for compactly supported data

This node collects the guarantees of Chen et al. for score-based diffusion sampling from a data distribution $q$ supported on a ball, which assume no density, no Lipschitz score and no finite KL divergence from the standard Gaussian: the DDPM sampler is stopped early.

## Expansion

A sound expansion has separate pages for:

1. **Early-stopped target.** If $q$ is supported on the ball of radius $R \ge 1$ and $0 < \varepsilon \ll \sqrt d$, the forward marginal $q_t$ at a time $t \asymp \varepsilon^2/(\sqrt d\,(R \vee \sqrt d))$ satisfies $W_2(q_t, q) \le \varepsilon$ and $\mathrm{KL}(q_t \Vert \gamma^d) \lesssim \sqrt d\,(R \vee \sqrt d)^3/\varepsilon^2$, and for every $t' \ge t$ the score of $q_{t'}$ is $L$-Lipschitz with $L \lesssim d R^2 (R \vee \sqrt d)^2/\varepsilon^4$.
2. **Guarantees.** Run backward for the time $T - t$ with a step size as in the DDPM guarantee, the output $p_{T-t}$ of the sampler is $\varepsilon_{\mathrm{TV}}$-close in total variation to $q_t$, where $t$ is set by $\varepsilon = \varepsilon_{W_2}$, when $N = \widetilde\Theta(d^3 R^4 (R \vee \sqrt d)^4/(\varepsilon_{\mathrm{TV}}^2 \varepsilon_{W_2}^8))$ and $\varepsilon_{\mathrm{score}} \le \widetilde O(\varepsilon_{\mathrm{TV}})$. With $t$ set by $\varepsilon$ and $\varepsilon_{\mathrm{score}} \le \widetilde O(\varepsilon)$, it is $\varepsilon$-close to $q$ in the bounded Lipschitz metric when $N = \widetilde\Theta(d^3 R^4 (R \vee \sqrt d)^4/\varepsilon^{10})$, and, projected onto the ball of radius $R_0 = \widetilde\Theta(R)$, it is $\varepsilon$-close to $q$ in $W_2$ when $N = \widetilde\Theta(d^3 R^8 (R \vee \sqrt d)^4/\varepsilon^{12})$.

## Sources

- Sampling is as easy as learning the score (Chen, Chewi, Li, Li, Salim, Zhang, ICLR 2023; arXiv:2209.11215), Section 3.2: Corollaries 3–5, and Lemma 20 of Appendix B. <https://arxiv.org/abs/2209.11215>
