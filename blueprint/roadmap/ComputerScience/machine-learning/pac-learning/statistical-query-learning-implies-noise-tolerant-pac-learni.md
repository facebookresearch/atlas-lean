# Statistical-query learning implies noise-tolerant PAC learning

In the statistical query model a learner asks queries $(\chi, \tau)$ with $\chi : X \times \{0,1\} \to \{0,1\}$
and tolerance $\tau > 0$, and receives any value within $\tau$ of $\mathbb{E}_{x \sim \mathcal{D}}[\chi(x,
c(x))]$. If a concept class is efficiently learnable from statistical queries (with $1/\tau$ and the query
evaluation time polynomially bounded), then it is efficiently PAC learnable under random classification
noise of every rate $\eta < 1/2$, with running time polynomial in $1/(1-2\eta)$ and the usual parameters.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: PAC learning under random classification noise of rate eta < 1/2.

## Depends on

- [Efficient PAC learning of representation classes](computational-complexity-of-learning/efficient-pac-learning-of-representation-classes.md)

## Sources

- M. Kearns, *Efficient noise-tolerant learning from statistical queries*, J. ACM 45(6) (1998) 983–1006, Theorems 1 and 3. <https://homepages.math.uic.edu/~lreyzin/papers/kearns98.pdf>
