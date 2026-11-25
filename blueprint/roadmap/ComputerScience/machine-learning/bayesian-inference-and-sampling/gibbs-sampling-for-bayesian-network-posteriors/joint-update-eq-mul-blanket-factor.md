# Joint probability splits off the Markov blanket factors

Let $B$ be a Bayesian network on the nodes $0, \dots, n-1$ (in topological order) with values in a nonempty type $\alpha$, with conditional probability tables $p_k(\cdot \mid x_{\mathrm{pa}(k)})$ and joint distribution $P(x) = \prod_{k} p_k(x_k \mid x_{\mathrm{pa}(k)})$. For a node $i$, let $\mathrm{ch}(i)$ be its children and $g_i(x) = p_i(x_i \mid x_{\mathrm{pa}(i)}) \prod_{k \in \mathrm{ch}(i)} p_k(x_k \mid x_{\mathrm{pa}(k)})$ the blanket factor. Then for every assignment $x$ and value $a \in \alpha$,

$$P\big(x[i \mapsto a]\big) = \Big(\prod_{k \notin \{i\} \cup \mathrm{ch}(i)} p_k(x_k \mid x_{\mathrm{pa}(k)})\Big)\; g_i\big(x[i \mapsto a]\big),$$

where $x[i \mapsto a]$ is $x$ with node $i$ set to $a$. The factors outside $\{i\} \cup \mathrm{ch}(i)$ do not depend on the value of node $i$.

## Sources

C. M. Bishop, *Pattern Recognition and Machine Learning*, Springer, 2006, Section 8.2, p. 382.
