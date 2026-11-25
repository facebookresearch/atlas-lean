# Evidence-weighted Dirichlet prior

Let $\alpha \in \mathbb{R}^{n+1}$ with $\alpha_i > 0$
for every $i$, and let $s$ be a sequence of $N$ labels in $\{0, \dots, n\}$ with label counts
$n_i(s)$. The Dirichlet distribution $\mathrm{Dir}(\alpha)$ weighted by the density
$\theta \mapsto P_\theta(s)$, the probability of $s$ under the multinomial sampling model with
parameter $\theta$, equals $B(\alpha + n(s)) / B(\alpha)$ times $\mathrm{Dir}(\alpha + n(s))$,
where $B$ is the multivariate Beta function and $\alpha + n(s)$ has entries $\alpha_i + n_i(s)$.
