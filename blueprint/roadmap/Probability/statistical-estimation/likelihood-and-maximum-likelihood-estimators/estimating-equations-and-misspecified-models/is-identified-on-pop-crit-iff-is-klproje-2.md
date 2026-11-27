# The pseudo-true value is the Kullback–Leibler projection, density form

Let $\nu$ be a $\sigma$-finite measure, the true law of $X_0$ (almost everywhere measurable, on a probability space) be $g\,\nu$, a probability measure with $g$ measurable and $\nu$-almost everywhere positive and $\log g$ integrable under the true law $g\,\nu$ (not under $\nu$), and for $\theta \in K$ let $P_\theta = p_\theta\,\nu$ be a probability measure with $p_\theta$ measurable, $\nu$-almost everywhere positive and $\log p_\theta$ integrable under the true law. Then $\theta^*$ uniquely maximizes $\theta \mapsto \mathbb{E}[\log p_\theta(X_0)]$ on $K$ if and only if it uniquely minimizes $\theta \mapsto \mathrm{KL}(g\nu \,\|\, P_\theta)$ on $K$.

This is the case $\mu_0 = g\,\nu$, $\mu_\theta = P_\theta$, $\ell_0 = \log g$, $\ell_\theta = \log p_\theta$ of [the general Kullback–Leibler projection result](is-identified-on-pop-crit-iff-is-klproje.md).
