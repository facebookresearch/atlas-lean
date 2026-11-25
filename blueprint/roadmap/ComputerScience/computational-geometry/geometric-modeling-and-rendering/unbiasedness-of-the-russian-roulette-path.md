# Unbiasedness of the Russian-roulette path estimator

Let $S$ be finite, $T$ a nonnegative $S \times S$ matrix, $E \in \mathbb{R}^S$ an emission vector, $P$ a row-stochastic matrix with $P_{ij} > 0$ whenever $T_{ij} > 0$, and $q \in (0, 1)^S$ stopping probabilities. From a start state $i$, generate a path $x_0 = i, x_1, \dots, x_N$: at each visited state $x_k$, stop with probability $q_{x_k}$ and otherwise move to $x_{k+1} = j$ with probability $P_{x_k j}$, so that the step $x_k \to j$ has probability $Q_{x_k j} = (1 - q_{x_k}) P_{x_k j}$. Define weights $W_0 = 1$, $W_{k+1} = W_k\, T_{x_k x_{k+1}} / Q_{x_k x_{k+1}}$ and the score $Z = \sum_{k=0}^{N} W_k E_{x_k}$. Then $N$ is almost surely finite with $\Pr[N \ge n] \le (1 - q_{\min})^n$. If the spectral radius of $T$ is less than $1$, then $Z$ is integrable and

$$\mathbb{E}[Z] = \Bigl(\sum_{k \ge 0} T^k E\Bigr)_i,$$

the $i$-th entry of the solution $I$ of $I = E + TI$. If moreover the matrix $K$ with $K_{ij} = T_{ij}^2/Q_{ij}$ (and $0$ where $Q_{ij} = 0$) has spectral radius less than $1$, then $Z$ has finite variance. Neither spectral condition can be dropped: for one state with $T = 1$, $E = P = 1$ and $q = 1/2$ the estimator terminates but the target diverges, and for $T = 1/2$, $E = P = 1$, $q = 4/5$ the target is finite but $K = 5/4$ and the second moment is infinite.

## Proof depends on

- [The rendering equation as a fixed-point equation](the-rendering-equation-as-a-fixed-point-equation.md)

## Expansion

This page becomes ready once:

- Neumann series: if the spectral radius of a square matrix T is below one, then I − T is invertible and its inverse is the convergent series of powers of T (proof prerequisite; not yet stated)

## Sources

- J. T. Kajiya, "The rendering equation", *SIGGRAPH 1986*, *Computer Graphics* 20(4):143–150, 1986
- M. Pharr, W. Jakob and G. Humphreys, *Physically Based Rendering*, 4th ed., MIT Press, 2023
