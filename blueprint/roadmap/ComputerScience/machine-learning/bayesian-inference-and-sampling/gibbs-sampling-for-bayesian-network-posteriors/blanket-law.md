# Local Gibbs update law from the Markov blanket factors

Let $B$ be a Bayesian network on the nodes $0, \dots, n-1$ (in topological order) with values in a finite nonempty type $\alpha$, with conditional probability tables $p_k(\cdot \mid x_{\mathrm{pa}(k)})$ and joint distribution $P(x) = \prod_{k} p_k(x_k \mid x_{\mathrm{pa}(k)})$. Assume all table entries are strictly positive. Let $E$ be a set of evidence nodes with values $e$, $i \notin E$ a free node and $z$ a configuration of the free nodes. For each node $j$ let $\mathrm{ch}(j)$ be its children and define the blanket factor

$$g_i(x) = p_i(x_i \mid x_{\mathrm{pa}(i)}) \prod_{k \in \mathrm{ch}(i)} p_k(x_k \mid x_{\mathrm{pa}(k)}) .$$

The update law of $z_i$ is the probability mass function on $\alpha$

$$a \mapsto \frac{g_i\big((e, z[i \mapsto a])\big)}{\sum_{a' \in \alpha} g_i\big((e, z[i \mapsto a'])\big)},$$

where $z[i \mapsto a]$ is $z$ with coordinate $i$ set to $a$ and $(e, z)$ the full assignment agreeing with $e$ on $E$ and $z$ off $E$. Positivity of the tables makes the normalizer positive.
