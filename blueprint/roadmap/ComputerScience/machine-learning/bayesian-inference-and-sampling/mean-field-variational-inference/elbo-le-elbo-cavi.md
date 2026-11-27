# The CAVI update maximizes the ELBO over the first factor

Let $A$ and $B$ be finite sets
with $A$ nonempty, let $p : A \times B \to \mathbb{R}$ be a joint, and let $q_1$ and $q_2$ be
probability distributions on $A$ and $B$. Let $q_1^*$ be the CAVI update of the first factor
given $q_2$, $q_1^*(a) = \exp E(a) / \sum_{a' \in A} \exp E(a')$ with
$E(a) = \sum_{b \in B} q_2(b) \log p(a, b)$. Then
$\mathrm{ELBO}(p, q_1 q_2) \le \mathrm{ELBO}(p, q_1^* q_2)$, where
$(q_1 q_2)(a, b) = q_1(a) q_2(b)$ and
$\mathrm{ELBO}(p, q) = \sum_{z} q(z) (\log p(z) - \log q(z))$.

Here $\log$ is the real logarithm extended by $\log x = \log |x|$ for $x < 0$ and $\log 0 = 0$.
