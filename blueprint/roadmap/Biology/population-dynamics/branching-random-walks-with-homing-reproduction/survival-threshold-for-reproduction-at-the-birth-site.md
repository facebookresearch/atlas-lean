# Survival threshold for a branching Markov chain that reproduces only at its birth site

**Model.** Let $\mathbf{X}$ be an irreducible discrete-time Markov chain on a countable set $S$ with transition probabilities $p(x,y)$, and fix a site $O\in S$ (the birth place). The branching Markov chain $\mathbf{Y}$ starts with one individual at $O$. At each time step every individual, independently, first dies with probability $1-\alpha$ ($\alpha\in(0,1]$ measures the leniency of the environment) and otherwise jumps according to $p(x,\cdot)$; each time an individual returns to $O$ it gives birth to one new individual at $O$, which follows the same dynamics. The process survives if some individual is alive at all times. Let $\beta$ be the probability that $\mathbf{X}$ started at $O$ ever returns to $O$, and $p_n(O,O)$ its $n$-step return probability.

**Theorem.**
- If $\beta\le 1/2$, $\mathbf{Y}$ dies out almost surely for every $\alpha\in(0,1)$ (and also for $\alpha = 1$).
- If $\beta>1/2$, there is $\alpha_c\in(0,1)$ such that $\mathbf{Y}$ survives with positive probability for $\alpha>\alpha_c$ and dies out for $\alpha\le\alpha_c$.

The critical value is the root of $\mu(\alpha_c) = 1$, where
$$
\mu(\alpha) = \sum_{n\ge 1}\alpha^n p_n(O,O).
$$
So a species without navigation, relying on chance to find its birth place, can persist in some environment iff a single individual in a perfectly lenient environment returns home with probability greater than $1/2$. A recurrent chain ($\beta=1$; e.g. simple random walk on $\mathbb{Z}$ or $\mathbb{Z}^2$) always allows survival for $\alpha$ close to 1, whereas simple random walk on $\mathbb{Z}^3$ ($\beta\approx 0.34$) never does. For the nearest-neighbour walk on $\mathbb{Z}$ with right-step probability $p$, $\beta = 1-|1-2p|$, so survival is possible iff $1/4<p<3/4$.

## Expansion

The genealogy of $\mathbf{Y}$ is a Bienaymé–Galton–Watson process $\mathbf{Z}$: an individual's children are its returns to $O$ before dying, and $\mathbf{Z}$ survives iff $\mathbf{Y}$ does. The mean offspring is $\mu(\alpha)$, which is continuous and strictly increasing with $\mu(0^+) = 0$, and by Abel's theorem for power series $\mu(\alpha)\to\sum_n p_n(O,O)$ as $\alpha\to 1^-$. If $\mathbf{X}$ is recurrent this sum is infinite, so $\mu$ crosses 1. If $\mathbf{X}$ is transient, at $\alpha = 1$ the number of returns is geometric, $\mathbb{P}(Z_1 = j) = (1-\beta)\beta^j$, so $\mu(1) = \beta/(1-\beta)$, which exceeds 1 iff $\beta>1/2$. The classical criterion (a BGW process with non-degenerate offspring survives with positive probability iff its mean exceeds 1) concludes.

## Sources

- R. B. Schinazi, "Can a rudderless species survive?", arXiv:2403.13874 (2024), Theorem 1 and its proof in Section 2 (using Lemma 2), <https://doi.org/10.48550/arXiv.2403.13874>.
