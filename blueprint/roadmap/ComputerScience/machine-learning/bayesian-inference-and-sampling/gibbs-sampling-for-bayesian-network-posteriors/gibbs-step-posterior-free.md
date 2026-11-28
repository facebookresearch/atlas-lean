# Gibbs update of a Bayesian-network posterior is the local sampler

Let $B$ be a Bayesian network on the nodes $0, \dots, n-1$ (in topological order) with values in a finite nonempty type $\alpha$, with conditional probability tables $p_k(\cdot \mid x_{\mathrm{pa}(k)})$ and joint distribution $P(x) = \prod_{k} p_k(x_k \mid x_{\mathrm{pa}(k)})$. Assume every table entry is strictly positive. Let $E \subseteq \{0, \dots, n-1\}$ be a set of evidence nodes with evidence values $e$; the free (non-evidence) variables are the configurations $z$ of the nodes outside $E$, and $(e, z)$ denotes the full assignment that equals $e$ on $E$ and $z$ off $E$. Write $P(e) = \sum_{x : x|_E = e|_E} P(x)$ for the evidence probability. Assume $P(e) \ne 0$, let $\pi(z) = P(z \mid X_E = e)$ be the posterior of the free variables (which has full support), and let $i \notin E$ be a free node. For every configuration $z$ of the free variables, the Gibbs update of coordinate $i$ from $z$ for the target $\pi$ (draw $s$ from $\pi(z_i = \cdot \mid z_{-i})$ and return $z[i \mapsto s]$) equals the law of $z[i \mapsto a]$ with $a$ drawn from the local update law

$$a \mapsto \frac{g_i\big((e, z[i \mapsto a])\big)}{\sum_{a'} g_i\big((e, z[i \mapsto a'])\big)},$$

where $g_i$ is the product of the table entries of node $i$ and of its children. This is the update step of the GIBBS-ASK procedure.

## Sources

S. Russell and P. Norvig, *Artificial Intelligence: A Modern Approach*, 4th ed., GIBBS-ASK.
