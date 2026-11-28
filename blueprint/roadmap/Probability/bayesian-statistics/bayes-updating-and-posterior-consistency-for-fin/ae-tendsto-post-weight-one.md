# Posterior consistency in a finite model

Let the parameter set $\Theta$ and the observation set $\mathcal{X}$ be finite. Let the prior $\pi \ge 0$ satisfy $\pi(\theta_0) > 0$, and let the likelihoods $f_\theta$ be strictly positive with $\sum_x f_\theta(x) = 1$ for each $\theta$, with positive Kullback-Leibler divergence $\sum_x f_{\theta_0}(x) \log\big(f_{\theta_0}(x)/f_\theta(x)\big) > 0$ for every $\theta \ne \theta_0$. Let $X_1, X_2, \dots$ be measurable observations on a probability space, pairwise independent, each with law $f_{\theta_0}$. Then almost surely the posterior weight

$$\frac{\pi(\theta_0) \prod_{i < n} f_{\theta_0}(X_i)}{\sum_{\theta} \pi(\theta) \prod_{i < n} f_\theta(X_i)}$$

tends to $1$ as $n \to \infty$.

## Sources

- J. L. Doob (1949); D. A. Freedman, Ann. Math. Statist. 34 (1963); S. Ghosal and A. van der Vaart, *Fundamentals of Nonparametric Bayesian Inference* (2017), Chapter 6.
