# Explicit formula for the full conditional of a Bayesian-network posterior

Let $B$ be a Bayesian network on the nodes $0, \dots, n-1$ (in topological order) with values in a finite nonempty type $\alpha$, with conditional probability tables $p_k(\cdot \mid x_{\mathrm{pa}(k)})$ and joint distribution $P(x) = \prod_{k} p_k(x_k \mid x_{\mathrm{pa}(k)})$. Assume every table entry is strictly positive. Let $E \subseteq \{0, \dots, n-1\}$ be a set of evidence nodes with evidence values $e$; the free (non-evidence) variables are the configurations $z$ of the nodes outside $E$, and $(e, z)$ denotes the full assignment that equals $e$ on $E$ and $z$ off $E$. Write $P(e) = \sum_{x : x|_E = e|_E} P(x)$ for the evidence probability. Assume $P(e) \ne 0$, let $\pi(z) = P(z \mid X_E = e)$ be the posterior of the free variables (which has full support), and let $i \notin E$ be a free node. For every configuration $z$ of the free variables and every value $a \in \alpha$, the conditional law of coordinate $i$ given the other free coordinates under $\pi$ is

$$\pi(z_i = a \mid z_{-i}) = \frac{g_i\big((e, z[i \mapsto a])\big)}{\sum_{a' \in \alpha} g_i\big((e, z[i \mapsto a'])\big)},$$

as real numbers, where $g_i(x) = p_i(x_i \mid x_{\mathrm{pa}(i)}) \prod_{k \in \mathrm{ch}(i)} p_k(x_k \mid x_{\mathrm{pa}(k)})$ is the product of the node's own table entry and its children's table entries.
