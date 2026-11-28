# Latent-factor Poisson neighbourhood regression

Let $X = (X_1, \dots, X_p)$ be the expression levels of $p$ genes and $G = (V, E)$ an undirected graph on $V = \{1, \dots, p\}$. A distribution of $X$ is **Markov** with respect to $G$ if $X_s$ and $X_t$ are conditionally independent given all other variables whenever $\{s, t\} \notin E$. If every node-conditional distribution belongs to an exponential family with sufficient statistic $B$ and base measure $C$, then any joint law with these conditionals has (Yang et al., 2012) the form

$$P(X) \propto \exp\Big(\sum_{s} \theta_s B(X_s) + \sum_{s}\sum_{t \in N(s)} \theta_{st} B(X_s)B(X_t) + \text{higher-order clique terms} + \sum_s C(X_s)\Big),$$

and in the pairwise case (cliques of size at most two) the edge set is $E = \{(s, t) : \theta_{st} \ne 0\}$. **Neighbourhood estimation** estimates each $N(s)$ by a regression of $X_s$ on the other variables and takes $\hat E = \bigcup_{s} \{(s, t) : t \in \hat N(s)\}$.

**Latent-factor Poisson neighbourhood model.** Fix a rank $r$. Each gene $s$ has a latent factor $u_s \in \mathbb{R}^r$ (its membership in $r$ latent components), and $W \in \mathbb{R}^{r \times r}$ encodes interactions between components. The model specifies, for each node, the Poisson log-linear regression

$$X_s \mid X_{V \setminus s} \sim \mathrm{Poisson}\Big(\exp\big\{\theta_s + \textstyle\sum_{t \ne s} \theta_{st} X_t\big\}\Big), \qquad \theta_{st} = u_s^{\top} W^{\top} W u_t ,$$

of $X_s$ on the other genes. The estimated neighbourhood is $\hat N(s) = \{t \ne s : \hat u_s^{\top} \hat W^{\top} \hat W \hat u_t \ne 0\}$. Given $n$ i.i.d. observations $x^{(1)}, \dots, x^{(n)}$, the parameters solve the penalized nodewise (pseudo-likelihood) problem

$$\min_{U, W}\ \sum_{s \in V} \ell_s(U, W) + \alpha\big(\mathrm{Reg}(U) + \mathrm{Reg}(W)\big), \qquad \ell_s = -\frac{1}{n}\sum_{i=1}^n \log P\big(X_s = x_s^{(i)} \mid X_{V\setminus s} = x_{V \setminus s}^{(i)}\big),$$

where $U = [u_1, \dots, u_p]$, $P(X_s = \cdot \mid X_{V\setminus s})$ is the Poisson law above, and $\mathrm{Reg}$ is an elastic-net penalty mixing a squared-norm term on the columns with an entrywise $\ell_1$ term, with mixing weight $\lambda \in [0, 1]$ controlling the sparsity of neighbourhoods. The objective is well defined for every $(U, W)$ as a sum of univariate Poisson regression losses.

**Joint law.** The node-conditional Poisson laws are the conditionals of a joint pairwise Poisson Markov network $P(x) \propto \exp\big(\sum_s \theta_s x_s + \sum_{s<t}\theta_{st}x_sx_t - \sum_s \log x_s!\big)$ on $\mathbb{N}^p$ only when this expression is normalizable, which holds if and only if $\theta_{st} \le 0$ for all $s \ne t$ (Besag's auto-Poisson restriction). The Gram factorization allows positive off-diagonal $\theta_{st}$: for two nodes with $\theta_{12} = 1$ and zero intercepts the weights on $(n, n)$ are proportional to $e^{n^2}/(n!)^2$, which do not even tend to zero. Without the nonpositivity restriction the method is therefore a nodewise fitting procedure, and its estimated graph is a set of regression neighbourhoods rather than the Markov graph of a joint distribution.

**Properties.**

- The edge weights are symmetric, $\theta_{st} = \theta_{ts}$: the contribution of $X_t$ to the law of $X_s$ equals that of $X_s$ to the law of $X_t$, as an undirected model requires, whereas separate node-wise regressions need not agree.
- The matrix $\Theta = (\theta_{st})$ equals $(WU)^{\top}(WU)$, a positive semidefinite Gram matrix of rank at most $r$, so the factorization also acts as a low-rank constraint on the network weights.
- Each conditional is the univariate Poisson law $P(X_s = x) = \mu^x e^{-\mu}/x!$ with mean $\mu = \exp\{\theta_s + \sum_{t \ne s}\theta_{st}X_t\}$; when all $\theta_{st} \le 0$ the conditionals define a multivariate Poisson graphical model whose Markov graph is $\{(s,t) : \theta_{st} \ne 0\}$.

## Expansion

Symmetry and the Gram form are immediate from $\theta_{st} = (Wu_s)^{\top}(Wu_t)$. For normalizable parameters the joint form follows the Hammersley–Clifford factorization over cliques: requiring every conditional to be an exponential family in its own sufficient statistic forces the clique potentials to be products of sufficient statistics, so learning the graph reduces to learning which pairwise weights are nonzero. Taking logs of the Poisson conditional gives $\log P(X_s \mid X_{V\setminus s}) = \eta_s X_s - \log X_s! - e^{\eta_s}$ with linear predictor $\eta_s = \theta_s + \sum_{t \ne s}\theta_{st}X_t$, so $\ell_s$ is the average Poisson regression loss and the penalized problem is a sparse regression in the factorized parameters whose parameters enter the edge weights bilinearly through the shared factors.

## Sources

- M. Žitnik and B. Zupan, "Gene network inference by fusing data from diverse distributions", Bioinformatics 31(12) (2015), i230–i239, Section 3.1 (Markov networks, exponential family, Eqs. (1)–(3)), Section 3.2 (Eqs. (4)–(5)), Sections 3.3–3.4 (Eqs. (6)–(9)), <https://doi.org/10.1093/bioinformatics/btv258> (PMC4542780).
- E. Yang, P. Ravikumar, G. I. Allen and Z. Liu, "Graphical models via generalized linear models", Advances in Neural Information Processing Systems 25 (2012), Poisson graphical model and its nonpositive pairwise-parameter restriction.
- J. Besag, "Spatial interaction and the statistical analysis of lattice systems", Journal of the Royal Statistical Society B 36 (1974) 192–236, auto-Poisson model.
