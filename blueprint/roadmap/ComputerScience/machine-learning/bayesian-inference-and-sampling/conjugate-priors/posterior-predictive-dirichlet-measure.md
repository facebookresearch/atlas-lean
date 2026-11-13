# Posterior predictive of the Dirichlet–multinomial model

Let $\alpha \in \mathbb{R}^{n+1}$
with $\alpha_i > 0$ for every $i$, and let $s$ be a sequence of $N$ labels in $\{0, \dots, n\}$
with label counts $n_i(s)$. Under the multinomial sampling model with the Dirichlet prior
$\mathrm{Dir}(\alpha)$, drawing a parameter from the posterior after observing $s$ and then one
label from the categorical likelihood gives the label $i$ with probability
$(\alpha_i + n_i(s)) / (\sum_j \alpha_j + N)$.

This is the Dirichlet–multinomial analogue of Laplace's rule of succession.
