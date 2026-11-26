# Swap agnostic learning and swap omniprediction

Let $D$ be a distribution over $X \times \{0,1\}$ with Bayes predictor $p^*(x) = \mathbb{E}[y \mid x]$, let $p : X \to [0,1]$ be a predictor, and let $\mathcal{C}$ be a collection of functions $c : X \to [-1,1]$ (indicators of subpopulations being the main example). **Swap agnostic learning** for a loss $\ell$ and class $\mathcal{C}$ is the game in which the learner selects a predictor $h$ and then an adversary selects, for each level set $\{x : h(x) = v\}$, a possibly different hypothesis $c_v \in \mathcal{C}$; the learner wins up to $\varepsilon$ if

$$
\mathbb{E}\big[\ell(h(x), y)\big] \le \mathbb{E}\big[\ell(c_{h(x)}(x), y)\big] + \varepsilon .
$$

A predictor $p$ is a **swap omnipredictor** for $(\mathcal{L}, \mathcal{C})$ if for every assignment $v \mapsto (\ell_v, c_v) \in \mathcal{L} \times \mathcal{C}$ of losses and hypotheses to level sets, $\sum_v \mathbb{E}[\mathbf{1}[p(x)=v](\ell_v(k_{\ell_v}(v), y) - \ell_v(c_v(x), y))] \le \varepsilon$; **swap multicalibration** requires multicalibration with an adversarially chosen $c_v$ for each level set.

## Depends on

- [Omnipredictors](omnipredictor.md)
- [Swap regret](../../../GameTheory/not-yet-classified/part-02/regret/swap-regret.md)

## Sources

- P. Gopalan, M. P. Kim, O. Reingold, "Swap Agnostic Learning, or Characterizing Omniprediction via Multicalibration", arXiv:2302.06726 (2023).
