# Concentration and asymptotic normality of rejection ABC in the Gaussian location model

Let $X_1,\ldots,X_n$ be independent $\mathcal N(\theta,1)$ under $P_\theta$, $\theta\in\mathbb R$, with summary $S_n=\frac1n\sum_iX_i$, and let the prior have a density $\pi$ that is continuous and positive at the true value $\theta_0$. For a tolerance $\varepsilon_n>0$, the rejection ABC posterior given the observed summary $s=S_n(x)$ is

$$\Pi_{\varepsilon_n}(d\theta\mid s)\propto\pi(\theta)\,P_\theta\bigl(|S_n-s|\le\varepsilon_n\bigr)\,d\theta .$$

Let the data be drawn under $P_{\theta_0}$ and $\varepsilon_n\to0$. Then:

1. *Concentration.* For every sequence $M_n\to\infty$,

    $$\Pi_{\varepsilon_n}\bigl(|\theta-\theta_0|>M_n\max(\varepsilon_n,n^{-1/2})\bigm| S_n\bigr)\to0\quad\text{in }P_{\theta_0}\text{-probability.}$$

2. *Asymptotic normality.* If $\varepsilon_n=o(n^{-1/2})$, then the total-variation distance between $\Pi_{\varepsilon_n}(\cdot\mid S_n)$ and $\mathcal N(S_n,1/n)$ tends to $0$ in $P_{\theta_0}$-probability.

A tolerance that does not tend to zero gives no concentration: for fixed $\varepsilon>0$, as $n\to\infty$ the ABC posterior converges to the prior restricted to $[\theta_0-\varepsilon,\theta_0+\varepsilon]$ and renormalized.

## Depends on

- [Rejection ABC returns the tolerance-conditioned posterior](abc-rejection-target-law-and-zero-tolerance-disc.md)

## Proof depends on

- [ABC with discrete summaries: exact limit and a model-choice counterexample](abc-with-discrete-summaries-exact-limit-and-a-mo.md)
- [Asymptotic normality of a consistent root of an estimating equation](../../../../Probability/statistical-estimation/asymptotic-normality-of-maximum-likelihood/tendsto-in-distribution-sqrt-mul-sub-of.md)

## Expansion

A full proof page must establish:

- The acceptance probability $L_n(\theta)=\Phi\bigl(\sqrt n(s+\varepsilon_n-\theta)\bigr)-\Phi\bigl(\sqrt n(s-\varepsilon_n-\theta)\bigr)$, its integral $\int L_n\,d\theta=2\varepsilon_n$, and the bound $L_n(\theta)\le2\varepsilon_n\sqrt n\,\varphi\bigl(\sqrt n(|\theta-s|-\varepsilon_n)^+\bigr)$ together with the Gaussian tail bound; with continuity of $\pi$ near $\theta_0$ and $S_n-\theta_0=O_P(n^{-1/2})$ these give part 1 in both regimes $\sqrt n\varepsilon_n\to\infty$ and $\sqrt n\varepsilon_n$ bounded.
- Part 2: $L_n(\theta)/(2\varepsilon_n\sqrt n)\to\varphi(\sqrt n(\theta-s))$ uniformly on the $n^{-1/2}$ scale when $\sqrt n\varepsilon_n\to0$, the Bernstein–von Mises theorem for the exact posterior given $S_n$, and the passage to total variation. The source's general theorem states convergence on sets; the total-variation form is a Gaussian-model computation.
- The fixed-tolerance counterexample.

## Sources

- D. T. Frazier, G. M. Martin, C. P. Robert and J. Rousseau, *Asymptotic properties of approximate Bayesian computation*, Biometrika (2018), <https://arxiv.org/abs/1607.06903>, Theorem 1 (posterior concentration with rate driven by $\varepsilon_T$ and the deviation of the summaries) and Theorem 2 (limiting shape: uniform when $v_T\varepsilon_T\to\infty$, Gaussian when $v_T\varepsilon_T\to0$).
