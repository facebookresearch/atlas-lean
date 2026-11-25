# Calibration of predictors and the calibrated-LM hallucination lower bound

This node collects calibration of binary predictors and the hallucination lower bound for calibrated
generative language models of Kalai and Vempala.

## Expansion

A sound expansion has separate pages for:

1. **Binary calibration.** A predictor $p : X \to [0,1]$ is calibrated if $\mathbb{E}[Y \mid p(X)] = p(X)$ almost
   surely; conditioning on the event $p(X) = v$ is not used, because such events may have probability zero.
2. **Model.** A finite set $Y$ of factoids, a finitely supported prior $\nu$ over distributions $p$ on $Y$
   (the random world), a generative model $g$ (a distribution on $Y$), and the miscalibration
   $\mathrm{Mis}_b(g, p)$ with respect to a partition of $Y$ into $b$ bins.
3. **Theorem 1** of the source: an inequality in expectation over $p \sim \nu$, for all sets of observed and
   unobserved facts and every partition, as stated in the source.
4. **Corollary 1** of the source: for every $\delta \in [0,1]$, $b, n \in \mathbb{N}$, $s \in \mathbb{R}$, every $s$-sparse regular world
   distribution and every algorithm, with probability at least $1 - \delta$ over the world and the $n$ training
   examples, the hallucination rate satisfies
   $g(H) \ge \widehat{MF} - \mathrm{Mis}_b(g, p) - 3e^{-s}/\delta - \sqrt{6\ln(6/\delta)/n}$, where $\widehat{MF}$ is the Good–Turing
   monofact estimate. The sparsity and regularity assumptions are essential.

## Sources

- A. T. Kalai and S. S. Vempala, *Calibrated language models must hallucinate*, STOC 2024 (arXiv:2311.14648): the world-distribution model, miscalibration $\mathrm{Mis}_b$, Theorem 1 and Corollary 1. <https://arxiv.org/pdf/2311.14648>
