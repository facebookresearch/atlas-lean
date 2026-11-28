# Entropic Gaussian mixture optimal transport and its zero-regularization limit

**Setting.** Cell populations at times $t_i$ and $t_{i+1}$ in gene-expression space $\mathbb{R}^n$ are fitted by Gaussian mixtures $\mu_{t_i} = \sum_{k=1}^{K_i} \pi_i^k\, \mathcal{N}(m_i^k, \Sigma_i^k)$ and $\mu_{t_{i+1}} = \sum_{l=1}^{K_{i+1}} \pi_{i+1}^l\, \mathcal{N}(m_{i+1}^l, \Sigma_{i+1}^l)$, components representing cell states. Between Gaussians the squared 2-Wasserstein distance is

$$W_2^2\big(\mathcal{N}(m_1, \Sigma_1), \mathcal{N}(m_2,\Sigma_2)\big) = \|m_1 - m_2\|^2 + \operatorname{tr}\Big(\Sigma_1 + \Sigma_2 - 2\big(\Sigma_1^{1/2}\Sigma_2\Sigma_1^{1/2}\big)^{1/2}\Big),$$

attained by the affine map $T(x) = m_2 + A(x - m_1)$, $A = \Sigma_1^{-1/2}(\Sigma_1^{1/2}\Sigma_2\Sigma_1^{1/2})^{1/2}\Sigma_1^{-1/2}$.

**Entropic Gaussian mixture OT.** For $\varepsilon > 0$, with $\Pi(\pi_i, \pi_{i+1}) = \{ w \in \mathbb{R}_{\ge 0}^{K_i \times K_{i+1}} : w\mathbf 1 = \pi_i,\ w^\top\mathbf 1 = \pi_{i+1}\}$ and $H(w) = -\sum_{k,l} w_{kl}(\log w_{kl} - 1)$,

$$d^\varepsilon_G(\mu_{t_i}, \mu_{t_{i+1}}) = \min_{w \in \Pi(\pi_i,\pi_{i+1})} \sum_{k,l} w_{kl}\, W_2^2\big(\mu_i^k, \mu_{i+1}^l\big) - \varepsilon H(w).$$

**Theorem.**

1. The problem has a unique solution of Sinkhorn form $w^\varepsilon_{kl} = u_k\, e^{-W_2^2(\mu_i^k, \mu_{i+1}^l)/\varepsilon}\, v_l$ with positive vectors $u, v$.

2. As $\varepsilon \to 0$, $w^\varepsilon$ converges exponentially fast to the maximum-entropy optimal plan $w^\ast$ of the unregularized problem: there is $M > 0$ with $\|w^\varepsilon - w^\ast\|_1 \le e^{-M/\varepsilon}$, and

    $$\big| d_G^\varepsilon - d_G^0 \big| \le \max_{k,l} W_2^2(\mu_i^k, \mu_{i+1}^l)\, e^{-M/\varepsilon} + (1 + \log K_i K_{i+1})\,\varepsilon .$$

3. The plan $\gamma^\ast(x,y) = \sum_{k,l} w^\ast_{kl}\, g_{m_i^k, \Sigma_i^k}(x)\, \delta_{y = T_{kl}(x)}$ minimizes the mixture-restricted Wasserstein problem $MW_2^2(\mu_{t_i}, \mu_{t_{i+1}}) = \inf\{ \int \|x - y\|^2 d\gamma : \gamma \text{ a Gaussian-mixture coupling of } \mu_{t_i}, \mu_{t_{i+1}} \}$; the entropic plans $\gamma^\varepsilon$ (same formula with $w^\varepsilon$) converge narrowly to $\gamma^\ast$, and $d^\varepsilon_G \to MW_2^2$ with the error bound of item 2.

## Expansion

The objective is linear plus $\varepsilon$ times a strongly convex negative entropy on a compact polytope, so the minimizer is unique; the first-order Lagrangian conditions give $\log w_{kl} = -W_{kl}/\varepsilon + \alpha_k/\varepsilon + \beta_l/\varepsilon$, the Sinkhorn scaling form, computable by alternating row and column normalization. Exponential convergence of entropic discrete OT to the maximum-entropy optimal vertex follows from the finite number of vertices of the transport polytope and the gap $M$ between the optimal and the next-best cost. Since any Gaussian-mixture coupling of two mixtures decomposes into Gaussian couplings of component pairs, the mixture-restricted problem reduces to discrete OT between components with Gaussian $W_2^2$ costs, which gives item 3. Downstream, the matrix $w^\varepsilon$ defines a cell-state graph between time points, the barycentric map $x \mapsto \sum_l w^\varepsilon_{kl} T_{kl}(x)/\pi_i^k$ on component $k$ gives cell velocities, and McCann-type interpolation $x \mapsto (1-s)x + sT_{kl}(x)$ animates intermediate expression states.

## Sources

- T. Yachimura, H. Wang, Y. Imoto, M. Yoshida, S. Tasaki, Y. Kojima, Y. Yabuta, M. Saitou and Y. Hiraoka, "scEGOT: single-cell trajectory inference framework based on entropic Gaussian mixture optimal transport", BMC Bioinformatics 25 (2024), 388, Results, Theory of EGOT (Eqs. (1)–(8), Propositions 1–2, Theorem 3), <https://doi.org/10.1186/s12859-024-05988-z>, PMCID: PMC11665215.
- J. Delon and A. Desolneux, "A Wasserstein-type distance in the space of Gaussian mixture models", SIAM Journal on Imaging Sciences 13 (2020), 936–970.
