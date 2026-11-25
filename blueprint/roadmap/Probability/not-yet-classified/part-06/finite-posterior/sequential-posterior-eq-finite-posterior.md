# Sequential and batch Bayesian updates agree

Let $\Theta$ be finite, let $\pi \ge 0$ be a prior with $\sum_\theta \pi(\theta) = 1$, and let $L_1, \dots, L_m$ be nonnegative likelihood functions. Write the posterior of weights $\pi$ under $L$ as $\pi(\theta)L(\theta)/\sum_{\theta'}\pi(\theta')L(\theta')$, taken as $0$ when the denominator is $0$. Updating $\pi$ by $L_1, \dots, L_m$ one at a time gives the posterior of $\pi$ under the product likelihood $\prod_j L_j$.
