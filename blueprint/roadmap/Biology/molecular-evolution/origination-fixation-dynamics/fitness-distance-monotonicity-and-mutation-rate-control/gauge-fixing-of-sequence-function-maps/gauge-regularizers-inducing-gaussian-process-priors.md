# Gauge regularizers inducing Gaussian process priors

Let $\mathcal A$ be an alphabet with $\alpha$ characters and consider sequences $x \in \mathcal A^\ell$. Index **weight space** by pairs $(S, s)$ with $S \subseteq [\ell]$ a set of positions and $s \in \mathcal A^{S}$ (including $S = \varnothing$), and define the $\alpha^\ell \times (\alpha+1)^\ell$ design matrix $\Phi_{x,(S,s)} = 1$ if $x[S] = s$ and $0$ otherwise, so that a weight vector $w$ represents the landscape $f = \Phi w$. The **gauge freedoms** are $G = \{w : \Phi w = 0\}$; a **linear gauge** is any subspace $\Theta$ complementary to $G$, in which every landscape has exactly one representative.

For training sequences $X$ with measurements $y$, a positive-definite $\Lambda$ gives the penalized estimate $w_{\mathrm{OPT}}(\Lambda, \beta) = \arg\min_w \|y - \Phi_X w\|_2^2 + \beta\, w^{\mathsf T}\Lambda w$. $\Lambda$ is a **$\Theta$-regularizer** if $w_{\mathrm{OPT}} \in \Theta$ for all $\beta > 0$, $X$ and $y$. $\Lambda$ **induces** the Gaussian process prior $f \sim \mathcal N(0, K)$ (positive-definite $K$) if $\Phi\, w_{\mathrm{OPT}}(\Lambda, \sigma_n^2)$ equals the MAP (posterior-mean) estimate of $f$ under $y = f_X + \varepsilon$, $\varepsilon \sim \mathcal N(0, \sigma_n^2 I)$, for every $\sigma_n^2 > 0$.

**Theorem.** For every linear gauge $\Theta$ and every positive-definite kernel $K$ on sequence space there is a $\Theta$-regularizer inducing $K$; one is

$$\Lambda = \Phi^{\mathsf T} K^{-1} \Phi + B^{\mathsf T} B,$$

where $B$ is any matrix with nullspace exactly $\Theta$.

**Orthogonalization criterion.** For complementary subspaces $V_1, V_2$, a positive-definite $\Lambda$ makes them $\Lambda$-orthogonal iff $\Lambda = A^{\mathsf T} A + B^{\mathsf T} B$ with $\operatorname{null}(A) = V_2$ and $\operatorname{null}(B) = V_1$; and any $\Lambda$ that orthogonalizes $\Theta$ and $G$ is a $\Theta$-regularizer.

## Depends on

- [Marginal law of the targets in Gaussian-process regression](../../../../../ComputerScience/machine-learning/supervised-learning/gaussian-process-regression/map-targets-eq.md)

## Proof depends on

- [Gaussian-process posterior mean is the kernel ridge fit](../../../../../Analysis/hilbert-spaces/gaussian-process-posterior-mean-is-the-kernel-ridge-fit.md)

## Expansion

Write any $w = \theta + g$ with $\theta \in \Theta$, $g \in G$. If $\Theta$ and $G$ are $\Lambda$-orthogonal, then $w^{\mathsf T}\Lambda w = \theta^{\mathsf T}\Lambda\theta + g^{\mathsf T}\Lambda g$ while the data term depends only on $\theta$ (since $\Phi g = 0$), so the optimum has $g = 0$. With $A = K^{-1/2}\Phi$, whose nullspace is $G$, and $B$ with nullspace $\Theta$, the criterion shows $\Lambda = \Phi^{\mathsf T}K^{-1}\Phi + B^{\mathsf T}B$ is a $\Theta$-regularizer. On $\Theta$ the penalty $B^{\mathsf T}B$ vanishes, so the objective becomes $\|y - f_X\|^2 + \beta f^{\mathsf T}K^{-1}f$ in terms of $f = \Phi\theta$, which is exactly the negative log posterior of Gaussian process regression with $\beta = \sigma_n^2$. The gauge part and the prior part of a regularizer thus act independently: the same prior can be paired with any gauge (for example the $\lambda$–$\pi$ family, interpolating between the trivial gauge and hierarchical, zero-sum-type gauges), and the posterior of the gauge-fixed weights follows by pushing the function-space posterior through the projection onto $\Theta$ along $G$.

## Sources

- S. Petti, C. Martí-Gómez, J. B. Kinney, J. Zhou, D. M. McCandlish, "On learning functions over biological sequence space: relating Gaussian process priors, regularization, and gauge fixing", *Journal of Mathematical Biology* (2026), Sections 2–3 (Definitions 1–6, Lemmas 1–5, Theorem 1), <https://doi.org/10.1007/s00285-026-02398-y> (PMC13128692).
