# Logarithmic sweep curve: from tents to houses

**Model.** Take the two-type Moran model with selective advantage $a\varphi_N$, exponent $b = \lim_N(-\log_N \varphi_N) \in [0,1)$ and a single initial mutant, as in [the fixation-time result](fixation-time-of-a-moderately-selected-sweep.md). The **logarithmic population sizes** are

$$H_i^N(t) = \log_N^{+}\!\Big(X_i^N\big(\tfrac{t \log N}{\varphi_N}\big)\Big), \qquad i \in \{0,1\},$$

with $\log_N^{+}(x) = \max\{\log_N x, 0\}$ and $(H_0^N, H_1^N) = (1, 0)$ for $t < 0$. Define the piecewise linear limits

$$h_1(t) = \begin{cases} 0, & t < 0,\\ b + at, & 0 \le t < \tfrac{1-b}{a},\\ 1, & t \ge \tfrac{1-b}{a},\end{cases} \qquad h_0(t) = \begin{cases} 1, & t < \tfrac{1-b}{a},\\ 2 - (b + at), & \tfrac{1-b}{a} \le t < \tfrac{2(1-b)}{a},\\ 0, & t \ge \tfrac{2(1-b)}{a}.\end{cases}$$

**Statement.** Conditional on fixation of the mutant, as $N \to \infty$:

1. for every $\varepsilon > 0$, $H_1^N \to h_1$ uniformly in probability on $\mathbb{R} \setminus [0, \varepsilon)$ and $H_0^N \to h_0$ uniformly in probability on $\mathbb{R} \setminus \big(\tfrac{2(1-b)}{a} - \varepsilon, \tfrac{2(1-b)}{a} + \varepsilon\big)$;
2. if $b = 0$ (strong or quasi-strong selection), the uniform convergence holds on all of $\mathbb{R}$, and the graph of $\min(h_0, h_1)$ is a "tent";
3. for every $b \in [0,1)$, $H_i^N \to h_i$ in probability in the Skorokhod $M_1$ topology on càdlàg paths $\mathbb{R} \to [0,1]$.

For $b \in (0,1)$ the limits jump by $b$ at $t = 0$ (mutant) and at $t = 2(1-b)/a$ (resident), so $\min(h_0, h_1)$ is a "house" with vertical walls. Convergence cannot hold in the $J_1$ topology, because the jumps of $H_i^N$ shrink to zero while the limit has a jump of size $b$.

## Depends on

- [Fixation time of a moderately selected sweep in the Moran model](fixation-time-of-a-moderately-selected-sweep.md)

## Expansion

On the time scale $\varphi_N^{-1}\log N$ a surviving mutant family climbs from size 1 to size $N^{b}$ in negligible time, which produces the jump of height $b$; it then grows like $N^{b + at}$, giving the slope $a$. The residents mirror this. Uniform convergence away from the walls comes from the branching-process couplings of the five phases. For $M_1$ convergence one shows that the climb over each wall is nearly monotone: the logarithm of a Bessel-like random walk (the mutant count viewed at its jump times) has running-maximum fluctuations that vanish on the $\log_N$ scale, so the path stays close in $M_1$ to its running maximum, which converges to the vertical wall.

## Sources

- F. Boenkost, F. Hermann, A. Tóbiás and A. Wakolbinger, Logarithmic scaling of selective sweep curves: from tents to houses, arXiv (2026). <https://doi.org/10.48550/arXiv.2605.10617> (Theorem 2.5 parts I.2, I.3 and II; Definition 2.4; Proposition 4.4; Remark 2.6.)
