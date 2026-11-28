# Ancestral sampling from a Bayesian network has the joint as its law

Let $B$ be a Bayesian network on the nodes $0, \dots, n-1$ with values in a finite nonempty type $\alpha$ and joint distribution $P(x) = \prod_k p_k(x_k \mid x_{\mathrm{pa}(k)})$. For every assignment $x \in \alpha^n$, the probability that ancestral sampling from $B$ returns $x$ is $P(x)$ (as an element of $[0, \infty]$).

## Sources

S. Russell and P. Norvig, *Artificial Intelligence: A Modern Approach*, 4th ed., Chapter 13, prior sampling.
