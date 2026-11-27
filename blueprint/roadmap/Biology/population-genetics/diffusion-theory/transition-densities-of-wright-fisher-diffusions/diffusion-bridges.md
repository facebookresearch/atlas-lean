# Wright–Fisher diffusion bridges

For the neutral Wright–Fisher diffusion with mutation parameters $\theta_1, \theta_2 > 0$ and transition density $f(x, y; t)$, the density at time $s$ of the bridge from $x$ at time $0$ to $z$ at time $t$ is

$$f_{z,t}(x, y; s) = \frac{f(x, y; s)\,f(y, z; t - s)}{f(x, z; t)}, \qquad 0 < s < t,$$

for $0 < x, y, z < 1$ (Jenkins and Spanò 2017, equation (11), citing Fitzsimmons, Pitman and Yor (1992) and Schraiber, Griffiths and Evans (2013)). Jenkins and Spanò (Proposition 2) write it as a mixture of Beta densities,

$$f_{z,t}(x, y; s) = \sum_{m=0}^\infty\sum_{k=0}^\infty\sum_{l=0}^m\sum_{j=0}^kp_{m,k,l,j}\,D_{\theta_1 + l + j,\ \theta_2 + m + k - l - j}(y),$$

where $D_{a,b}$ is the Beta$(a, b)$ density and the weights

$$p_{m,k,l,j} = B_{m,x}(l)\,D_{\theta_1 + j,\ \theta_2 + k - j}(z)\,DM_{\theta_1 + l,\ \theta_2 + m - l;\ k}(j)\,\frac{q^\theta_m(s)\,q^\theta_k(t - s)}{f(x, z; t)}$$

form a probability mass function on $\mathbb N^4$ (equation (13)); here $B_{m,x}$ is the Binomial$(m, x)$ mass function, $DM_{a,b;k}(j) = \binom kjB(a + j, b + k - j)/B(a, b)$ the beta-binomial mass function, and $q^\theta_m(t)$ the probability that the ancestral line-counting process started from infinitely many lines has $m$ lines at time $t$ (Section 2). Drawing $(M, K, L, J)$ from these weights and then $Y$ from the corresponding Beta law gives exact samples from the bridge (Algorithm 4), and nonneutral bridges are simulated by rejection with the neutral bridge as candidate (Section 6).

## Depends on

- [Exact simulation of the Wright–Fisher diffusion](../../../../Biology/population-genetics/diffusion-theory/transition-densities-of-wright-fisher-diffusions/exact-simulation-of-the-wright-fisher-diffusion.md)
- [Jacobi series of the Wright–Fisher transition density with mutation](jacobi-series-of-the-mutation-transition-density.md)
- [Beta-mixture marginals for every mutation Wright-Fisher solution](line-of-descent-mixture-representation-of-the-tr.md)
- [Finite and entrance transition probabilities for the mutation line-count process](transition-probabilities-q-theta-n-t-of-the-non.md)

## Expansion

1. The bridge law by the kernel formula for interior endpoints, and its Markov property.
2. The mixture representation of the neutral transition density over the ancestral line-counting process.
3. Proposition 2: the Beta-mixture form of the bridge density, by Bayes' rule and beta-binomial conjugacy.
4. Exact sampling from the four-index weights with finitely many evaluated terms.
5. Bridges that end at $0$ or $1$, obtained by conditioning on events of positive probability, as separate statements.

## Sources

- P. A. Jenkins and D. Spanò, Exact simulation of the Wright–Fisher diffusion, Ann. Appl. Probab. 27 (2017), 1478–1509, Section 2, Section 3.1, equations (11)–(13), Proposition 2, Algorithm 4 and Section 6. <https://doi.org/10.1214/16-AAP1236> <https://arxiv.org/abs/1506.06998>
