# Bayesian skyline coalescent prior

Let $g$ be a rooted genealogy of $n$ contemporaneously sampled sequences with coalescent intervals $t_2, \dots, t_n$, where $t_k$ is the length of the interval during which $k$ lineages exist. Fix a number $m$ of groups ($1 \le m \le n-1$) and a vector of group sizes $A = (A_1, \dots, A_m)$ of positive integers with $\sum_j A_j = n - 1$. Assign the coalescent intervals in order, from the tips to the root, to consecutive groups, so that group $j$ contains $A_j$ intervals, and let $c(k)$ be the group of the interval with $k$ lineages. Each group carries an effective population size parameter $\Theta_j > 0$ (effective size times generation time), constant within the group. The **Bayesian skyline** likelihood of the genealogy is

$$p(g \mid \Theta, A) = \prod_{k=2}^n \frac{\binom{k}{2}}{\Theta_{c(k)}} \exp\Bigl( -\binom{k}{2} \frac{t_k}{\Theta_{c(k)}} \Bigr),$$

a piecewise-constant coalescent. The prior on $\Theta$ is a chain: $p(\Theta_1) \propto 1/\Theta_1$, and given $\Theta_{j-1}$, $\Theta_j$ is exponential with mean $\Theta_{j-1}$. This smooths changes in population size between adjacent groups. The group sizes $A$ have a uniform prior, and the joint posterior of $(g, \Theta, A)$ and the substitution-model parameters given a sequence alignment $D$ is

$$p(g, \Theta, A, \text{model} \mid D) \propto p(D \mid g, \text{model})\; p(g \mid \Theta, A)\; p(\Theta)\; p(A)\; p(\text{model}),$$

sampled by MCMC. The posterior distribution of the effective population size through time is read off by averaging the piecewise-constant trajectories across samples. With $m = n - 1$ (every group one interval) the likelihood factor becomes the classic skyline model; with $m = 1$ it is the constant-size coalescent.

## Depends on

- [Log-likelihood of one coalescent interval in the skyline model](skyline-log-lik.md)
- [Classic skyline estimate of population size](skyline-estimate.md)

## Expansion

Within a period of constant size $\Theta$, each of the $\binom{k}{2}$ pairs of lineages coalesces at rate $1/\Theta$. So the waiting time with $k$ lineages is exponential with rate $\binom{k}{2}/\Theta$, and the interval lengths are independent, which gives the product form. Grouping intervals pools their information about one $\Theta_j$, which reduces the noise of the classic skyline. The exponential chain prior makes consecutive group sizes positively dependent without fixing a parametric growth model.

## Sources

- A. J. Drummond, A. Rambaut, B. Shapiro and O. G. Pybus, *Bayesian coalescent inference of past population dynamics from molecular sequences*, Mol. Biol. Evol. 22 (2005), 1185–1192, <https://doi.org/10.1093/molbev/msi103> (the Bayesian skyline model: grouped piecewise-constant coalescent likelihood, Jeffreys and exponential-chain prior on group sizes, joint MCMC with the genealogy).
