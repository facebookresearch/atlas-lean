# The summed second moments split at any round

Fix a learning rate $\eta$ and $n$ experts.
For a finite sequence $\sigma$ of loss vectors in $\mathbb{R}^n$ and weights $w \in \mathbb{R}^n$,
write $Q(\sigma, w)$ for the sum over the rounds of $\sigma$ of the weighted second moments of the
losses, started from $w$, and $W(\sigma, w)$ for the weights after the rounds of $\sigma$ started
from $w$. Then for all such sequences $\sigma, \sigma'$ and all weights $w$,
$Q(\sigma\sigma', w) = Q(\sigma, w) + Q(\sigma', W(\sigma, w))$.
