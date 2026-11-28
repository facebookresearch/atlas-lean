# Detailed balance

Let $H$ be a finite set of hypotheses with prior $\pi$, $D$ a finite set of data, and $L(h)$ a probability distribution on $D$ for each hypothesis $h$. The transmission kernel $K$ of iterated learning satisfies detailed balance with respect to the prior: $\pi(h) K(h, h') = \pi(h') K(h', h)$ for all hypotheses $h, h'$.
