# Asymptotics of the hybrid incentive cost

**Setting.** Take the finite-population model and the hybrid cost $E_{\mathrm{mix}}(\theta)$ of [hybrid reward–punishment incentives](hybrid-incentive-cost-and-cooperation-threshold.md), with population size $N$, selection intensity $\beta$, payoff difference $\delta < 0$ and efficiency ratios $a, b > 0$. Define

$$H_{N,a,b} = \sum_{j=1}^{N-1}\frac{1}{j(N-j)}\min\Big(\frac{j}{a}, \frac{N-j}{b}\Big).$$

**Theorem.**

1. *Boundedness.* $H_{N,a,b}$ is bounded in $N$ and

$$\lim_{N\to\infty} H_{N,a,b} = H_{a,b} = \frac1a\ln\frac{a+b}{b} + \frac1b\ln\frac{a+b}{a}.$$

Consequently, for fixed $\theta > 0$, $E_{\mathrm{mix}}(\theta)$ grows quadratically in $N$; explicitly, for $N \ge 3$,

$$\frac{N^2\theta}{2}\Big(H_{N,a,b} + \frac{1}{\max(a,b)(N-1)}\Big) \le E_{\mathrm{mix}}(\theta) \le N(N-1)\theta\Big(H_{N,a,b} + \frac{1}{\min(a,b)\lfloor (N-1)/2\rfloor}\Big),$$

and for $N = 2$ the only transient state is left with probability $1/4$ per update, so $E_{\mathrm{mix}}(\theta) = 4\theta/\max(a,b)$ exactly, for every $\beta$.
2. *Neutral drift limit.* $\lim_{\beta\to0}E_{\mathrm{mix}}(\theta) = \theta N^2 H_{N,a,b}$.
3. *Strong selection limit.*

$$\lim_{\beta\to\infty}E_{\mathrm{mix}}(\theta) = \begin{cases} \dfrac{N^2\theta}{2}\Big(H_{N,a,b} + \dfrac{1}{N-1}\min\Big(\dfrac1a, \dfrac{N-1}{b}\Big)\Big), & \theta < -\delta, \\[2ex] \dfrac{N^2\theta}{2}\Big(H_{N,a,b} + \dfrac{1}{N-1}\min\Big(\dfrac{N-1}{a}, \dfrac1b\Big)\Big), & \theta > -\delta. \end{cases}$$

The minima do not simplify in general: at $(N,a,b) = (4,1,10)$ the first endpoint term is $1/10$, not $1/(a(N-1)) = 1/3$. At $\theta = -\delta$ the transition probabilities are neutral for every $\beta$, so $E_{\mathrm{mix}}(-\delta) = -\delta N^2 H_{N,a,b}$ as in part 2. (This corrects Theorem 1(iii) and Proposition 6 of Duong, Durbac and Han (2023) as printed, which write "$\lim_{\beta\to+\infty} E_{\mathrm{mix}}(\theta) = \frac{N^2\theta}{2}(H_{N,a,b} + \frac{1}{a(N-1)})$, for $\theta < -\delta$", "$\frac{N^2\theta}{2}[H_{N,a,b} + \frac{1}{b(N-1)}]$ for $\theta > -\delta$", and for $\theta = -\delta$ the expression "$\frac{NA}{2}[2N H_{N,a,b} + \frac{1}{a(N-1)} + \frac{1}{b(N-1)} - \frac{\min(2/a,(N-2)/b)}{2(N-2)} - \frac{\min((N-1)/a,1/b)}{N-1}]$"; the corrected limits follow directly from the proof's displays $\eta_0 = H_{N,a,b} + h_0$ with $h_0 = \min(1/a, (N-1)/b)/(N-1)$, $\eta_{N-1} = H_{N,a,b} + h_{N-2}$, and $\sum_j \eta_j = 2N H_{N,a,b}$. Likewise, part 1 and the phase-transition theorem restrict Theorem 1(i) and Theorem 2 to $N \ge 3$ and state $N = 2$ separately, departing from the printed Theorem 1(i) whose upper bound divides by $\lfloor (N-1)/2 \rfloor = 0$ at $N = 2$ and the printed "since $N \ge 2$" before Theorem 2.)
4. *Infinite population limit.* For the donation game with cost $c$,

$$\lim_{N\to\infty}\frac{E_{\mathrm{mix}}(\theta)}{N^2\theta H_{a,b}/2} = 1 + e^{-\beta|\theta - c|},$$

and for the public goods game $c$ is replaced by $c(1 - r/n)$.

**Phase transition ($a = b$, $N \ge 3$).** Admissible incentives are $\theta \ge \theta_{\min} = \max(0, \theta_0(\omega))$. There is an explicit threshold $\beta^* > 0$, defined through a pair of polynomials in $u = e^{x}$, such that $\theta \mapsto E_{\mathrm{mix}}(\theta)$ is non-decreasing for $\beta \le \beta^*$, so the optimal incentive is the smallest admissible one, $\theta^* = \theta_{\min}$; for $\beta > \beta^*$ the cost is not monotone, and for small $N$ it increases, decreases and increases again, so the optimum is $\theta_{\min}$ or, if the interior local minimizer is admissible (at least $\theta_{\min}$), the cheaper of the two. The case $N = 2$ is excluded: there $E_{\mathrm{mix}}(\theta) = 4\theta/a$ is linear at every selection intensity, so $\theta^* = \theta_{\min}$ and no transition occurs.

## Depends on

- [Hybrid reward–punishment incentives and the cooperation threshold](hybrid-incentive-cost-and-cooperation-threshold.md)

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

In the neutral limit the transition probabilities are $u_{i,i\pm1} = i(N-i)/(2N^2)$; the jump chain is a simple symmetric walk with Green's function $2i(N-j)/N$ ($i \le j$), and the expected sojourn per visit is $N^2/(i(N-i))$, which gives $n_{1j} + n_{N-1,j} = 2N^2/(j(N-j))$ and hence part 2. For part 1, $\min(j/a, (N-j)/b)/(j(N-j))$ equals $1/(a(N-j))$ below the crossover $j^* = Na/(a+b)$ and $1/(bj)$ above it; the two harmonic tails converge to $\frac1a\ln\frac{N}{N-j^*}$ and $\frac1b\ln\frac{N}{j^*}$, which gives $H_{a,b}$ and, unlike the separate reward or punishment problems (which carry the harmonic number $\sim\ln N$), no logarithmic growth. In the strong-selection limit the chain moves deterministically toward full cooperation when $\theta > -\delta$ and toward full defection when $\theta < -\delta$. For $\theta > -\delta$ the walk from $1$ visits every $j$ once, with mean sojourn $N^2/(j(N-j))$, and the walk from $N-1$ visits only $j = N-1$, adding the boundary term $\frac{N^2}{N-1}\min\big(\frac{N-1}{a}, \frac1b\big)$; for $\theta < -\delta$ the roles are reversed and the extra term sits at $j = 1$, weighted by $\min\big(\frac1a, \frac{N-1}{b}\big)$. For $N = 2$, $u_{1,0} + u_{1,2} = 1/4$ for every $\beta$, so $n_{11} = 4$ and $E_{\mathrm{mix}} = \frac{\theta}{2}(4 + 4)\min(1/a, 1/b)$.

## Sources

- M. H. Duong, C. M. Durbac and T. A. Han, "Cost optimisation of hybrid institutional incentives for promoting cooperation in finite populations", Journal of Mathematical Biology 87 (2023), Section 2, Equation (8), Theorems 1 and 2, and Propositions 4–7, <https://doi.org/10.1007/s00285-023-02011-6> (PMC10603005).
