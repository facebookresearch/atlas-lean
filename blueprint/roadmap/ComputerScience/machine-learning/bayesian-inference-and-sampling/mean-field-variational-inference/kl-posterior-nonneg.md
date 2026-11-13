# The KL divergence to the posterior is nonnegative

Let $Z$ be a nonempty finite set, let
$p : Z \to \mathbb{R}$ satisfy $p(z) > 0$ for every $z \in Z$, and let $q$ be a probability
distribution on $Z$. Let $\pi(z) = p(z) / \sum_{z' \in Z} p(z')$ be the posterior of $p$. Then
$\mathrm{KL}(q \,\|\, \pi) = \sum_{z \in Z} q(z) \bigl(\log q(z) - \log \pi(z)\bigr) \ge 0$.
