# Posterior weights are the Bayes update by the product likelihood

Let $\Theta$ be a finite set, $\pi : \Theta \to \mathbb{R}$ prior weights, $f : \Theta \times \mathcal X \to \mathbb{R}$ likelihoods and $X_0, X_1, \dots$ observations in $\mathcal X$. Write $w_n(\theta) = \pi(\theta)\prod_{i<n} f(\theta, X_i) / \sum_{\theta'} \pi(\theta')\prod_{i<n} f(\theta', X_i)$ for the posterior weight after $n$ observations (with $x/0 = 0$). Then $w_n$ is the Bayes update of $\pi$ by the likelihood $\theta \mapsto \prod_{i<n} f(\theta, X_i)$, for every $n$ and every sample.
