# A sweep of coordinate ascent does not decrease the ELBO

Let $A$ and $B$ be nonempty
finite sets, let $p : A \times B \to \mathbb{R}$ be a joint, and let $q_1$ and $q_2$ be probability
distributions on $A$ and $B$. One sweep replaces $q_1$ by its CAVI update $q_1'$ given $q_2$ and
then $q_2$ by its CAVI update $q_2'$ given $q_1'$, where
$q_1'(a) \propto \exp \sum_{b} q_2(b) \log p(a, b)$ and
$q_2'(b) \propto \exp \sum_{a} q_1'(a) \log p(a, b)$, each normalized to sum to $1$. Then
$\mathrm{ELBO}(p, q_1 q_2) \le \mathrm{ELBO}(p, q_1' q_2')$, where
$(q_1 q_2)(a, b) = q_1(a) q_2(b)$ and
$\mathrm{ELBO}(p, q) = \sum_{z} q(z) (\log p(z) - \log q(z))$.

Here $\log$ is the real logarithm extended by $\log x = \log |x|$ for $x < 0$ and $\log 0 = 0$.
