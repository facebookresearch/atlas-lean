# Law of a structural causal model

Let $M$ be a Markovian structural causal model on the nodes $0, \dots, n - 1$ with values in
$\alpha$ and disturbances in a finite set $\beta$ with laws $\pi_k$. The law of the endogenous
variables is the image of the product law of the disturbances by the solution map:
$P(x) = \sum_{u \in \beta^n} \prod_k \pi_k(u_k) \, \mathbf{1}[X(u) = x]$ for $x \in \alpha^n$.
