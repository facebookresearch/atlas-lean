# Bayes risk over a finite action space

Let the parameter space $\Theta$ be a nonempty standard Borel space, the action space $\mathcal Y$ finite and nonempty, and the loss $\ell : \Theta \times \mathcal Y \to [0,\infty]$ measurable. Let $P$ be a finite kernel from $\Theta$ to the data space and $\pi$ a finite prior. Then the Bayes risk equals

$$\int \min_{y \in \mathcal Y} \int \ell(\theta, y)\,\pi_x(d\theta)\;(P\circ\pi)(dx),$$

where $\pi_x$ is the posterior given $x$ and $P\circ\pi$ is the marginal law of the data.
