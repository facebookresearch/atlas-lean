# Neutral mutant fixation on a line in a random environment

**Line model.** Sites $1,\dots,N$ on a line each hold a normal or a mutant cell. Fitnesses are random and independent of each other: at site $k$ the normal fitness is $\mu_k = 1 + \delta B_k$ and the mutant fitness is $\nu_k = 1 + \delta B'_k$, where $B_1,\dots,B_N,B'_1,\dots,B'_N$ are independent fair $\pm1$ (Rademacher) variables and $\delta \in (0,1)$; so the mutant is *selectively neutral on average*. Each cell attempts to reproduce into each neighbouring site at rate $1$, an attempt across the mutant–normal boundary succeeding with a probability determined by the local fitnesses. Starting from one mutant at site $1$, the mutants always occupy an interval $[1,k]$, and the right end performs a birth–death chain on $\{0,\dots,N\}$ absorbed at $0$ and $N$, with

$$p_k = \frac{\beta_{k+1}}{\beta_{k+1} + (1-\beta_k)}, \qquad \beta_k = \frac{\mu_k}{\nu_k + \mu_k}.$$

Let $G(\delta)$ be the event of mutant fixation (absorption at $N$) and $\mathbb P_N$ the annealed law (averaging over the environment). Without randomness ($\delta = 0$) the fixation probability is $1/N$.

**Theorem.** If $N \to \infty$ with $\delta\sqrt N \to c > 0$, then

$$N\,\mathbb P_N\big(G(\delta)\big) \to g(c) = \mathbb E\Big[\frac{1}{\int_0^1 \exp\big(\sqrt2\,c\,B_s\big)\,ds}\Big],$$

for a standard Brownian motion $B$. The function $g$ is continuous and strictly increasing on $(0,\infty)$ with $g(c) - 1 \sim c^2/6$ as $c \downarrow 0$ and $g(c) \sim c/\sqrt\pi$ as $c \to \infty$. If instead $\delta\sqrt N \to \infty$ while $\delta(\log N)^{\epsilon} \to 0$ for some $\epsilon>0$, then

$$\mathbb P_N\big(G(\delta)\big) \sim \frac{\delta}{\sqrt{\pi N}}.$$

So environmental randomness gives an on-average neutral minority invader a fixation advantage over $1/N$ that grows with $N$ and $\delta$.

**Theorem (balanced environments).** For $N$ even, conditionally on $\sum_j B_j = \sum_j B'_j$ the fixation probability is exactly $1/N$ for every $\delta$: the advantage comes entirely from environments that are favorable to the mutant overall, not from local pockets of favorability that cancel out.

## Depends on

- [Existence of Brownian motion](../../../../Probability/stochastic-calculus/construction-and-sample-paths-of-brownian-motion/exists-is-brownian-real.md)

## Proof depends on

- [Hitting probabilities of finite birth–death chains](../../../../Probability/markov-chains/finite-continuous-time-markov-chains/hitting-times-of-finite-continuous-time-markov-c/hitting-probabilities-and-stationary-laws-of-bir.md)

## Expansion

For a birth–death chain, $\mathbb P_1(\tau_N < \tau_0) = \big(\sum_{k=0}^{N-1}\prod_{j=1}^k \frac{q_j}{p_j}\big)^{-1}$. In the random environment $\log\prod_{j\le k} q_j/p_j$ is, to first order in $\delta$, a random walk with steps of size $\delta$ built from the $B$'s and $B'$'s, so for $\delta\sqrt N \to c$ it converges to $\sqrt2\,c\,B_{k/N}$ and the sum becomes $N\int_0^1 e^{\sqrt2 cB_s}ds$. The Matsumoto–Yor formulas for exponential functionals of Brownian motion give the asymptotics of $g$.

## Sources

- Suzan Farhang-Sardroodi, Natalia L. Komarova, Marcus Michelen and Robin Pemantle, "Success probability for selectively neutral invading species in the line model with a random fitness landscape", arXiv:2005.13491 (2020), Theorem 1, Theorem 2, Theorem 4, Proposition 5 (birth–death absorption formula), Lemma 6 (scaling limit) and Proposition 7 (Matsumoto–Yor), <https://doi.org/10.48550/arXiv.2005.13491>; published in *Studies in Applied Mathematics* 146(4) (2021) 1023–1049, <https://doi.org/10.1111/sapm.12373>. Locators follow arXiv v2.
