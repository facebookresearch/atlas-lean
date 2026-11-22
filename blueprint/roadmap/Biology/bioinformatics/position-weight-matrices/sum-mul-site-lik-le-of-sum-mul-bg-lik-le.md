# Thresholding the log-odds score is most powerful

Let $p_i(b) > 0$ and $q(b) > 0$ for all $i, b$, let $t$ be real, and let $\phi$ be a function on sites with $0 \le \phi \le 1$ and

$$\sum_s \phi(s)\, \beta(s) \le \sum_s [\,t < \mathrm{sc}_L(s)\,]\, \beta(s),$$

where $\beta$ is the [background likelihood](bg-lik.md), $L$ the [log-odds matrix](log-odds.md) and $\mathrm{sc}$ the [score](score.md). Then $\sum_s \phi(s)\, \lambda(s) \le \sum_s [\,t < \mathrm{sc}_L(s)\,]\, \lambda(s)$, where $\lambda$ is the [site likelihood](site-lik.md).
