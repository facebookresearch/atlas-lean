# The ELBO is a lower bound

Let $Z$ be a finite set and let $p : Z \to \mathbb{R}$ satisfy
$p(z) > 0$ for all $z$, with evidence $p(x) = \sum_{z \in Z} p(z)$. Then for every probability
distribution $q$ on $Z$,

$$\mathrm{ELBO}(p, q) = \sum_{z \in Z} q(z) (\log p(z) - \log q(z)) \le \log p(x).$$

This is Gibbs' inequality.
