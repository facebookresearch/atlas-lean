# Auto-logistic conditionals of a pathway Markov random field

**Model.** A pathway is an undirected graph $(V,E)$ on genes $1,\dots,N$; $N_i$ is the neighbour set of gene $i$. Each gene has an unknown label $x_i \in \{-1,1\}$ ($1$ = associated). The prior is a nearest-neighbour Gibbs measure of the form

$$\pi(x) = \frac{1}{Z(\Phi)} \exp\Big( h \sum_{i} I(x_i = 1) + \beta_0 \sum_{(i,j)\in E} w_{ij}\, I(x_i = x_j = -1) + \beta_1 \sum_{(i,j)\in E} w_{ij}\, I(x_i = x_j = 1) \Big),$$

with hyperparameters $\Phi = (h,\beta_0,\beta_1)$, fixed nonnegative edge weights $w_{ij}$ and normalizing constant $Z(\Phi)$ summing over all $2^N$ labelings. For $\beta_0 = \beta_1 = 0$ the labels are independent with $P(x_i = 1) = e^h/(1+e^h)$. The data are gene-level statistics $y_i$, conditionally independent given $x$, with density $f_1$ if $x_i = 1$ and $f_0$ if $x_i = -1$.

**Proposition.**
1. The prior is a Markov random field: $\pi(x_i \mid x_{-i}) = \pi(x_i \mid x_{N_i})$, and non-adjacent genes are conditionally independent given all others. Its full conditional is auto-logistic,

$$\log\frac{\pi(x_i = 1 \mid x_{N_i})}{\pi(x_i = -1 \mid x_{N_i})} = h + \beta_1 \sum_{j \in N_i} w_{ij}\, I(x_j = 1) - \beta_0 \sum_{j \in N_i} w_{ij}\, I(x_j = -1).$$

2. The posterior $p(x \mid y) \propto \pi(x)\prod_i f_{x_i}(y_i)$ is also a Markov random field on the same graph, with conditional log odds equal to the prior conditional log odds plus the marginal log likelihood ratio $\log\big(f_1(y_i)/f_0(y_i)\big)$.
3. Iterated conditional modes, which sets each $x_i$ in turn to the maximizer of $p(x_i \mid x_{-i}, y)$, never decreases $p(x \mid y)$ and so converges to a local maximum of the posterior.
4. With marginal posterior probabilities $p_i = P(x_i = 1 \mid y)$, the rule $\delta_i = I(p_i > 1/2)$ minimizes the posterior expected $0$–$1$ loss; to keep the posterior expected false discovery rate at most $\alpha$, sort $p_{(1)} \ge p_{(2)} \ge \cdots$ and call the top $k$ genes for the largest $k$ with $\frac1k \sum_{l=1}^k (1 - p_{(l)}) \le \alpha$.

## Depends on

- [Local Markov property](../../../../../ComputerScience/not-yet-classified/markov-random-field/local-markov.md)

## Proof depends on

- [Gibbs factorization implies the global Markov property](../../../../../ComputerScience/not-yet-classified/markov-random-field/global-markov-of-gibbs-factorization.md)
- [Local Markov of global Markov](../../../../../ComputerScience/not-yet-classified/markov-random-field/local-markov-of-global-markov.md)

## Expansion

In the ratio $\pi(x_i = 1, x_{-i})/\pi(x_i = -1, x_{-i})$ every term of the exponent not involving $i$ cancels, as does $Z(\Phi)$; only the field term and the edges at $i$ remain, which gives the auto-logistic form and the Markov property. Multiplying by the factorized likelihood adds a single-site term, so the posterior keeps the same neighbourhood structure, and its closed-form conditionals make the Gibbs sampler and ICM cheap. The ICM step maximizes $p(x_i \mid x_{-i},y)$ while $p(x_{-i} \mid y)$ is unchanged, so the joint posterior is monotone. The FDR rule uses that $\sum_{l\le k} (1-p_{(l)})$ is the posterior expected number of false discoveries among the top $k$.

## Sources

- M. Chen, J. Cho, H. Zhao, "Incorporating biological pathways via a Markov random field model in genome-wide association studies", PLoS Genetics 7(4):e1001353 (2011), Eqs (1)–(6), Proposition 1 with Eqs (7)–(8), and the posterior Markov property with Eqs (9)–(10), <https://doi.org/10.1371/journal.pgen.1001353>, PMCID PMC3072362.
