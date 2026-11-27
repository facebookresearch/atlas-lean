# AdaBoost is greedy coordinate descent on the exponential loss

AdaBoost runs on $m > 0$ training points with labels $y_i \in \{\pm 1\}$ and an arbitrary weak learner; $D_t$ are its weights, $h_t$ the weak hypothesis and $\varepsilon_t$ its weighted error in round $t$, $\alpha_t = \tfrac12 \log((1-\varepsilon_t)/\varepsilon_t)$, and $F_T = \sum_{t<T} \alpha_t h_t$ is the combined score. Suppose the round's error satisfies $0 < \varepsilon_T \le 1/2$. Then for every hypothesis $h$ whose weighted error $\varepsilon$ under $D_T$ lies in $[\varepsilon_T, 1 - \varepsilon_T]$, and for every step $a \in \mathbb{R}$,

$$L(F_{T+1}) \le L(F_T + a h),$$

where $L$ is the [exponential loss](exp-loss.md). Two readings:

- with $h = h_T$, the step $\alpha_T$ is an exact line search along the chosen coordinate;
- if the weak learner returns a hypothesis of minimum weighted error from a class closed under negation, every $h$ in the class satisfies the condition, so AdaBoost takes the best coordinate step available: it is greedy coordinate descent on $L$, with the hypotheses as coordinates.

This is Breiman's observation, recalled in "Explaining AdaBoost". Schapire stresses there that minimizing the exponential loss is not by itself what makes AdaBoost generalize: other minimizers of the same loss can generalize badly, and AdaBoost's behaviour on the margins (see [the margin bound on the training sample](margin-err-le.md)) is a separate part of the explanation.

## Background

- [Regret of entropic mirror descent for prediction with expert advice](../../../../Analysis/convex-analysis-and-variations/mirror-descent/multiplicative-weights-regret-le.md): AdaBoost's reweighting $D_{t+1}(i) \propto D_t(i)\, e^{-\alpha_t y_i h_t(x_i)}$ is the multiplicative-weights update over the training points with loss vector $(y_i h_t(x_i))_i$ and step $\alpha_t$, the entropic prox step of mirror descent; boosting runs it on examples, Hedge on experts.

## Sources

- R. E. Schapire, "Explaining AdaBoost", in B. Schölkopf, Z. Luo and V. Vovk (eds.), *Empirical Inference: Festschrift in Honor of Vladimir N. Vapnik*, Springer (2013), Section 4 (where the observation is credited to Breiman).
