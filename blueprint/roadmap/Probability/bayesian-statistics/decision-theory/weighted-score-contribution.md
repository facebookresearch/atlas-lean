# Weighted-score Bayes rule for finite binary decisions

Given $P_0, P_1 : \mathcal{X} \to \mathbb{R}$, reals $\pi, c_{\mathrm{FP}}, c_{\mathrm{FN}}$ and a randomization level $a \in \mathbb{R}$, the per-observation contribution at $x \in \mathcal{X}$ is

$$a\, S_1(x) + (1 - a)\, S_0(x), \qquad S_1(x) = (1 - \pi)\, c_{\mathrm{FP}}\, P_0(x), \quad S_0(x) = \pi\, c_{\mathrm{FN}}\, P_1(x),$$

that is, $a (1 - \pi) c_{\mathrm{FP}} P_0(x) + (1 - a)\, \pi\, c_{\mathrm{FN}} P_1(x)$.
