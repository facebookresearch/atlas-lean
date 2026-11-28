# Posterior weight after n observations

Let $\Theta$ be a finite set of parameters with prior weights $\pi$, let $f(\theta, x)$ be likelihoods and $X_0, X_1, \dots$ observations. The posterior weight of $\theta$ after the first $n$ observations is

$$w_n(\theta) = \frac{\pi(\theta) \prod_{i<n} f(\theta, X_i)}{\sum_{\theta'} \pi(\theta') \prod_{i<n} f(\theta', X_i)},$$

with $x/0 = 0$.
