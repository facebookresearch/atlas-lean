# The CAVI update of the second factor does not decrease the ELBO

Let $A$ and $B$ be finite
sets with $B$ nonempty, let $p : A \times B \to \mathbb{R}$ be a joint, and let $q_1$ and $q_2$ be
probability distributions on $A$ and $B$. Let $q_2^*$ be the CAVI update of the second factor
given $q_1$, $q_2^*(b) = \exp F(b) / \sum_{b' \in B} \exp F(b')$ with
$F(b) = \sum_{a \in A} q_1(a) \log p(a, b)$. Then
$\mathrm{ELBO}(p, q_1 q_2) \le \mathrm{ELBO}(p, q_1 q_2^*)$, where
$(q_1 q_2)(a, b) = q_1(a) q_2(b)$ and
$\mathrm{ELBO}(p, q) = \sum_{z} q(z) (\log p(z) - \log q(z))$.

Here $\log$ is the real logarithm extended by $\log x = \log |x|$ for $x < 0$ and $\log 0 = 0$.
