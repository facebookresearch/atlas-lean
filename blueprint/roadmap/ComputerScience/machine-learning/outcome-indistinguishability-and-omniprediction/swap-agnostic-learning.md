# Swap agnostic learning and swap omniprediction

Let $D$ be a distribution over $X \times \{0,1\}$ with Bayes predictor $p^*(x) = \mathbb{E}[y \mid x]$, let $p : X \to [0,1]$ be a predictor, and let $\mathcal{C}$ be a collection of functions $c : X \to [-1,1]$ (indicators of subpopulations being the main example). **Swap agnostic learning** for a loss $\ell$ and class $\mathcal{C}$ is the game in which the learner selects a predictor $h$ and then an adversary selects, for each level set $\{x : h(x) = v\}$, a possibly different hypothesis $c_v \in \mathcal{C}$; the learner wins up to $\varepsilon$ if, writing $c_{h(x)}$ for the hypothesis chosen on the level set of $h(x)$,

$$
\mathbb{E}\big[\ell(h(x), y)\big] \le \mathbb{E}\big[\ell(c_{h(x)}(x), y)\big] + \varepsilon .
$$

Conditional expectations given $p(x) = v$ below are regular conditional expectations and are averaged over $v \sim p(x)$ (the law of the forecast), so no level needs positive mass: a forecast with a nonatomic law has no level of positive probability, and a sum over levels would be zero. A predictor $p$ is a **swap omnipredictor** for $(\mathcal{L}, \mathcal{C})$ with error $\varepsilon$ if for every assignment $v \mapsto \ell_v \in \mathcal{L}$ of losses to levels, $\mathbb{E}_{v \sim p(x)}\big[\mathbb{E}[\ell_v(k_{\ell_v}(v), y) \mid p(x) = v]\big] \le \mathbb{E}_{v \sim p(x)}\big[\inf_{c \in \mathcal{C}} \mathbb{E}[\ell_v(c(x), y) \mid p(x) = v]\big] + \varepsilon$, so the comparison hypothesis may also depend on the level; for a predictor with countably many values this is the sum $\sum_v \Pr[p(x) = v]\,(\cdots)$ over its levels; $p$ is **$(\mathcal{C}, \alpha)$-swap multicalibrated** if $\mathbb{E}_{v \sim p(x)}\big[\max_{c \in \mathcal{C}} |\mathbb{E}[c(x)(y - v) \mid p(x) = v]|\big] \le \alpha$, which strengthens $(\mathcal{C}, \alpha)$-multicalibration $\max_{c \in \mathcal{C}} \mathbb{E}_{v}\big|\mathbb{E}[c(x)(y - v) \mid p(x) = v]\big| \le \alpha$ by exchanging the maximum and the expectation. A swap omnipredictor is a swap agnostic learner (with $h = k_\ell \circ p$) for every $\ell \in \mathcal{L}$, hence an omnipredictor.

## Depends on

- [Omnipredictors](omnipredictor.md)
- [Swap regret](../../../GameTheory/not-yet-classified/part-02/regret/swap-regret.md)

## Sources

- P. Gopalan, M. P. Kim, O. Reingold, "Swap Agnostic Learning, or Characterizing Omniprediction via Multicalibration", NeurIPS (2023), arXiv:2302.06726, Definitions 2.1, 2.4, 2.6 and 2.7, Claims 2.2, 2.5 and 2.8.
