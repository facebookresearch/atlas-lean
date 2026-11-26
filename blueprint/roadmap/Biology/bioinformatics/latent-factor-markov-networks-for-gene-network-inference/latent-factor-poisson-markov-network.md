# Latent-factor Poisson Markov network

Let $X = (X_1, \dots, X_p)$ be the expression levels of $p$ genes and $G = (V, E)$ an undirected graph on $V = \{1, \dots, p\}$. A distribution of $X$ is **Markov** with respect to $G$ if $X_s$ and $X_t$ are conditionally independent given all other variables whenever $\{s, t\} \notin E$. If every node-conditional distribution belongs to an exponential family with sufficient statistic $B$ and base measure $C$, the joint law has (Yang et al., 2012) the form

$$P(X) \propto \exp\Big(\sum_{s} \theta_s B(X_s) + \sum_{s}\sum_{t \in N(s)} \theta_{st} B(X_s)B(X_t) + \text{higher-order clique terms} + \sum_s C(X_s)\Big),$$

and in the pairwise case (cliques of size at most two) the edge set is $E = \{(s, t) : \theta_{st} \ne 0\}$. **Neighbourhood estimation** estimates each $N(s)$ by a regression of $X_s$ on the other variables and takes $\hat E = \bigcup_{s} \{(s, t) : t \in \hat N(s)\}$.

**Latent-factor Poisson model.** Fix a rank $r$. Each gene $s$ has a latent factor $u_s \in \mathbb{R}^r$ (its membership in $r$ latent components), and $W \in \mathbb{R}^{r \times r}$ encodes interactions between components. The node-conditional laws are

$$X_s \mid X_{V \setminus s} \sim \mathrm{Poisson}\Big(\exp\big\{\theta_s + \textstyle\sum_{t \ne s} \theta_{st} X_t\big\}\Big), \qquad \theta_{st} = u_s^{\top} W^{\top} W u_t ,$$

a Poisson log-linear regression of $X_s$ on the other genes. The estimated neighbourhood is $\hat N(s) = \{t \ne s : \hat u_s^{\top} \hat W^{\top} \hat W \hat u_t \ne 0\}$. Given $n$ i.i.d. observations $x^{(1)}, \dots, x^{(n)}$, the parameters solve the penalized conditional maximum-likelihood problem

$$\min_{U, W}\ \sum_{s \in V} \ell_s(U, W) + \alpha\big(\mathrm{Reg}(U) + \mathrm{Reg}(W)\big), \qquad \ell_s = -\frac{1}{n}\sum_{i=1}^n \log P\big(X_s = x_s^{(i)} \mid X_{V\setminus s} = x_{V \setminus s}^{(i)}\big),$$

where $U = [u_1, \dots, u_p]$ and $\mathrm{Reg}$ is an elastic-net penalty mixing a squared-norm term on the columns with an entrywise $\ell_1$ term, with mixing weight $\lambda \in [0, 1]$ controlling the sparsity of neighbourhoods.

**Properties.**

- The edge weights are symmetric, $\theta_{st} = \theta_{ts}$: the contribution of $X_t$ to the law of $X_s$ equals that of $X_s$ to the law of $X_t$, as an undirected model requires, whereas separate node-wise regressions need not agree.
- The matrix $\Theta = (\theta_{st})$ equals $(WU)^{\top}(WU)$, a positive semidefinite Gram matrix of rank at most $r$, so the factorization also acts as a low-rank constraint on the network weights.
- Each conditional is the univariate Poisson law $P(X_s = x) = \mu^x e^{-\mu}/x!$ with mean $\mu = \exp\{\theta_s + \sum_{t \ne s}\theta_{st}X_t\}$, so the model extends the univariate Poisson to a multivariate graphical model.

## Expansion

Symmetry and the Gram form are immediate from $\theta_{st} = (Wu_s)^{\top}(Wu_t)$. The joint form follows the Hammersley–Clifford factorization over cliques: requiring every conditional to be an exponential family in its own sufficient statistic forces the clique potentials to be products of sufficient statistics, so learning the graph reduces to learning which pairwise weights are nonzero. Taking logs of the Poisson conditional gives $\log P(X_s \mid X_{V\setminus s}) = \eta_s X_s - \log X_s! - e^{\eta_s}$ with linear predictor $\eta_s = \theta_s + \sum_{t \ne s}\theta_{st}X_t$, so $\ell_s$ is the average Poisson regression loss and the penalized problem is a sparse regression in the factorized parameters whose parameters enter the edge weights bilinearly through the shared factors.

## Sources

- M. Žitnik and B. Zupan, "Gene network inference by fusing data from diverse distributions", Bioinformatics 31(12) (2015), i230–i239, Section 3.1 (Markov networks, exponential family, Eqs. (1)–(3)), Section 3.2 (Eqs. (4)–(5)), Sections 3.3–3.4 (Eqs. (6)–(9)), <https://doi.org/10.1093/bioinformatics/btv258> (PMC4542780).
- E. Yang, P. Ravikumar, G. I. Allen and Z. Liu, "Graphical models via generalized linear models", Advances in Neural Information Processing Systems 25 (2012).
