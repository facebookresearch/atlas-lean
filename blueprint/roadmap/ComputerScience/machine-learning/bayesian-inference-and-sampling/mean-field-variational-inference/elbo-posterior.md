# The ELBO bound is attained at the posterior

Let $Z$ be a nonempty finite set and let
$p : Z \to \mathbb{R}$ satisfy $p(z) > 0$ for all $z$, with evidence $p(x) = \sum_{z \in Z} p(z)$
and posterior $p(z \mid x) = p(z) / p(x)$. Then $\mathrm{ELBO}(p, p(\cdot \mid x)) = \log p(x)$,
where $\mathrm{ELBO}(p, q) = \sum_{z} q(z) (\log p(z) - \log q(z))$.
