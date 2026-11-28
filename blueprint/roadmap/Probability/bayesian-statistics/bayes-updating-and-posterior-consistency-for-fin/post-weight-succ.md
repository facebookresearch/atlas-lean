# One more observation updates the posterior weights

Let $\Theta$ be a finite set, $\pi : \Theta \to \mathbb{R}$ prior weights, $f : \Theta \times \mathcal X \to \mathbb{R}$ likelihoods and $X_0, X_1, \dots$ observations in $\mathcal X$. Write $w_n(\theta) = \pi(\theta)\prod_{i<n} f(\theta, X_i) / \sum_{\theta'} \pi(\theta')\prod_{i<n} f(\theta', X_i)$ for the posterior weight after $n$ observations (with $x/0 = 0$). If the evidence $\sum_\theta \pi(\theta) \prod_{i<n} f(\theta, X_i)$ is nonzero, then $w_{n+1}$ is the Bayes update of $w_n$ by the likelihood $\theta \mapsto f(\theta, X_n)$.
