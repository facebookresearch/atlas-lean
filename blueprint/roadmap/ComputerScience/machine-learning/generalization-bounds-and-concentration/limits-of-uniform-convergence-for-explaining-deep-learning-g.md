# Limits of uniform convergence for explaining deep-learning generalization

This node collects the construction of Nagarajan and Kolter showing that uniform convergence can fail to
explain generalization.

## Expansion

A sound expansion has separate pages for:

1. **Setting.** Uniform-convergence bounds restricted to the hypotheses an algorithm actually outputs, for a
   high-dimensional linear task (item 2) and a ReLU-network task (Section 3.2 of the source, a separate page).
2. **Result** (Theorem 3.1 of the source). Inputs are $(x_1, x_2) \in \mathbb{R}^K \times \mathbb{R}^D$; for a fixed $u \in \mathbb{R}^K$ with
   $\lVert u \rVert = 1/\sqrt m$, the label $y$ is uniform on $\{\pm 1\}$, $x_1 = 2yu$ and $x_2 \sim N(0, \tfrac{32}{D} I)$ independently. The
   learner starts at $w = 0$ and takes one gradient step of rate $1$ on $\sum_{(x,y) \in S} y\langle w, x\rangle$, so
   $w = (2mu, \sum_i y^{(i)} x_2^{(i)})$. With the ramp loss $L^{(\gamma)}$, let $\epsilon_{\mathrm{gen}}(m, \delta)$ be the least $\epsilon$
   with $\Pr_S[\lvert L_D(h_S) - \hat L_S(h_S)\rvert \le \epsilon] \ge 1 - \delta$, and $\epsilon_{\mathrm{unif\text{-}alg}}(m, \delta)$ the least $\epsilon$ for which
   some set $\mathcal{S}_\delta$ of samples of probability at least $1 - \delta$ has
   $\sup_{S \in \mathcal{S}_\delta} \sup_{h \in \{h_{S'} : S' \in \mathcal{S}_\delta\}} \lvert L_D(h) - \hat L_S(h)\rvert \le \epsilon$. Then for all $\epsilon > 0$ and $0 < \delta \le 1/4$,
   when $D = \Omega(\max\{m\ln(m/\delta), m\ln(1/\epsilon)\})$ and $\gamma \in [0, 1]$, $\epsilon_{\mathrm{gen}}(m, \delta) \le \epsilon$ while
   $\epsilon_{\mathrm{unif\text{-}alg}}(m, \delta) \ge 1 - \epsilon$; and for every $\gamma \ge 0$, $\epsilon_{\mathrm{unif\text{-}alg}} \ge 1 - \epsilon_{\mathrm{gen}}$.
3. **Scope.** The conclusion concerns these constructions; it is not a claim about all deep-learning
   settings.

## Depends on

- [Uniform convergence property and eps-representative samples](../pac-learning/agnostic-pac-learning-and-uniform-convergence/uniform-convergence-property-and-eps-representative-samples.md)

## Sources

- Uniform convergence may be unable to explain generalization in deep learning (Nagarajan & Kolter, NeurIPS 2019; arXiv:1902.04742) — arXiv / NeurIPS: Definitions 3.1–3.3, the setup of Section 3.1 and Theorem 3.1; Section 3.2 for the network variant. <https://arxiv.org/abs/1902.04742>
