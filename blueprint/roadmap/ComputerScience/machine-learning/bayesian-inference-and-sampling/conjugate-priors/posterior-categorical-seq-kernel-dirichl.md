# Dirichlet–multinomial conjugacy

Let $\alpha \in \mathbb{R}^{n+1}$ with $\alpha_i > 0$
for every $i$, and let $s$ be a sequence of $N$ labels in $\{0, \dots, n\}$ with label counts
$n_i(s)$. Under the multinomial sampling model with the Dirichlet prior $\mathrm{Dir}(\alpha)$,
the posterior distribution of the parameter after observing $s$ is the Dirichlet distribution
with parameters $\alpha_i + n_i(s)$.
