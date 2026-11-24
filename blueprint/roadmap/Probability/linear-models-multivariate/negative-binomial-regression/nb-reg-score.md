# Joint score of negative binomial regression

For a joint parameter $(\beta, \theta)$ and an observation $(x, y)$, with $\eta = x^\top\beta$, the joint score has coefficient block $\frac{\theta(y - e^\eta)}{\theta + e^\eta}\,x$ and shape coordinate $\partial_\theta\log\mathrm{NB}(y; \theta, e^\eta)$.
