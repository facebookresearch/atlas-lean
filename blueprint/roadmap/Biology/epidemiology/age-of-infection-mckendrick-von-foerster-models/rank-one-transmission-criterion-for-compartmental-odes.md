# Rank-one transmission criterion for compartmental ODE models

Let $\mathcal{S}$ be a finite set of infected compartments and consider the compartmental model

$$\dot n_i(t) = S(t)\sum_{j\in\mathcal{S}} \beta_{ji}\, n_j(t) + \sum_{j\in\mathcal{S}} q_{ji}\, n_j(t), \qquad S(t) = 1 - \sum_{j\in\mathcal{S}} n_j(t),$$

where $\beta_{ij} \ge 0$ is the rate at which an individual in compartment $i$ creates new infections that start in compartment $j$ (transmission matrix $T = (\beta_{ij})$), and $Q = (q_{ij})$ is a transition-rate matrix with $q_{ij} \ge 0$ for $i \ne j$ and $q_{ii} = -\sum_{j\ne i} q_{ij}$.

Suppose $\operatorname{rank}(T) = 1$, so that $\beta_{ij} = \lambda_i p_j$ for rates $\lambda_i \ge 0$ and a probability vector $(p_j)_{j\in\mathcal{S}}$. Let $X$ be the Markov chain with generator $Q$ and initial law $(p_j)$, put $p(a,i) = \mathbb{P}(X(a) = i)$ and $\tau(a) = \sum_{i} \lambda_i\, p(a,i)$, and let $n(t,a)$ solve the age-of-infection PDE with this $\tau$. Then $\tilde n_i(t) = \int_0^\infty n(t,a)\,p(a,i)\,da$ solves the ODE system. Conversely, every decorated age-of-infection model with a Markov life cycle and infection rates $\lambda_i \ge 0$ in compartment $i$ gives an ODE system with $\beta_{ij} = \lambda_i\,p(0,j)$, an outer product of $(\lambda_i)$ with a probability vector, which has rank at most one, and rank exactly one when some $\lambda_i > 0$ (if all $\lambda_i = 0$, then $T = 0$). Models whose transmission matrix has rank greater than one, such as models with assortative contacts between groups, cannot be written as a single decorated age-structured PDE.

## Depends on

- [Decorated age-of-infection model and compartment counts](decorated-age-of-infection-model-and-compartment-counts.md)

## Proof depends on

- [Kolmogorov forward equation](../../../Probability/markov-chains/finite-continuous-time-markov-chains/the-transition-semigroup-of-a-finite-continuous/has-deriv-at-ctmc-transition-forward.md)

## Expansion

Differentiate $\tilde n_i$, use $\partial_t n = -\partial_a n$, and integrate by parts. This gives $\dot{\tilde n}_i = n(t,0)\,p(0,i) + \int_0^\infty n(t,a)\,\partial_a p(a,i)\,da$. Kolmogorov's forward equation gives $\partial_a p(a,i) = \sum_j q_{ji}\,p(a,j)$, which produces the $Q$ term. The boundary condition gives $n(t,0) = S(t)\sum_j \lambda_j \tilde n_j(t)$, so the infection term is $S(t)\sum_j \lambda_j p_i \tilde n_j$, that is $\beta_{ji} = \lambda_j p_i$. A rank-one $T$ factors as $\lambda_i = \sum_j \beta_{ij}$ and $p_j = \beta_{ij}/\lambda_i$, and the factorization is the same for every $i$ with $\lambda_i > 0$. This is the separable-mixing condition of Diekmann and coauthors. It covers SIR, SEIR and every model in which new infections enter a single compartment.

## Sources

- F. Foutel-Rodier, F. Blanquart, P. Courau, P. Czuppon, J.-J. Duchamps, J. Gamblin, É. Kerdoncuff, R. Kulathinal, L. Régnier, L. Vuduc, A. Lambert, E. Schertzer, *From individual-based epidemic models to McKendrick–von Foerster PDEs: a guide to modeling and inferring COVID-19 dynamics*, Journal of Mathematical Biology 85 (2022), 43, <https://doi.org/10.1007/s00285-022-01794-4>, PMCID PMC9517997. Proposition 3 and its proof (connection with ODE models, Eq. (7)).
