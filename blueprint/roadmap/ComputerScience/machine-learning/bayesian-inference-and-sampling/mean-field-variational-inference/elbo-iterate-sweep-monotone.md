# Mean-field coordinate ascent never decreases the ELBO

Let $A$ and $B$ be nonempty finite
sets, let $p : A \times B \to \mathbb{R}$ be a joint, and let $q_1^{(0)}$ and $q_2^{(0)}$ be
probability distributions on $A$ and $B$. A sweep of coordinate ascent replaces $q_1$ by its CAVI
update $q_1'(a) \propto \exp \sum_{b} q_2(b) \log p(a, b)$ and then $q_2$ by its CAVI update
$q_2'(b) \propto \exp \sum_{a} q_1'(a) \log p(a, b)$, each normalized to sum to $1$. Let
$(q_1^{(t)}, q_2^{(t)})$ be the result of $t$ sweeps from $(q_1^{(0)}, q_2^{(0)})$. Then
$t \mapsto \mathrm{ELBO}(p, q_1^{(t)} q_2^{(t)})$ is monotone on $\mathbb{N}$, where
$(q_1 q_2)(a, b) = q_1(a) q_2(b)$ and
$\mathrm{ELBO}(p, q) = \sum_{z} q(z) (\log p(z) - \log q(z))$.

Here $\log$ is the real logarithm extended by $\log x = \log |x|$ for $x < 0$ and $\log 0 = 0$.
