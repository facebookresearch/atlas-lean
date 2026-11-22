# AdaBoost's reweighting is a normalized Hedge step

Let $D$ be positive weights on $m > 0$ training points with labels $y$, and let $h$ be a hypothesis with weighted error $\varepsilon$ under $D$. Write $\ell_i = 1$ if $h(x_i) = y_i$ and $\ell_i = 0$ otherwise. Then AdaBoost's reweighting is Hedge's update with learning rate $\eta = \log((1-\varepsilon)/\varepsilon)$ and losses $\ell$, normalized:

$$D'_i = \frac{D_i\, e^{-\alpha y_i h(x_i)}}{Z} = \frac{D_i\, e^{-\eta \ell_i}}{\sum_j D_j\, e^{-\eta \ell_j}}, \qquad \alpha = \tfrac12 \log\frac{1-\varepsilon}{\varepsilon}.$$

In Freund and Schapire's notation $e^{-\eta} = \beta_t = \varepsilon_t/(1-\varepsilon_t)$ and the update is $w_i^{t+1} = w_i^t \beta_t^{1 - |h_t(x_i) - y_i|}$: the training points play the experts, and a point's "loss" is $1$ when the weak hypothesis classifies it correctly, so that weight moves to the hard points. The difference from Hedge is that $\beta_t$ is chosen afresh in each round from $\varepsilon_t$.

## Background

- [Hedge algorithm](../hedge-algorithm/README.md): the multiplicative-weights algorithm over experts whose update this is.

## Sources

- Y. Freund and R. E. Schapire, "A decision-theoretic generalization of on-line learning and an application to boosting", *J. Comput. System Sci.* 55 (1997), 119–139, Figure 2 (steps 4 and 5) and the comparison with Hedge($\beta$) in Section 4.2.
