# Phase transition in the optimal per-capita incentive

**Model.** A well-mixed population of $N$ players, cooperators (C) and defectors (D), plays the donation game (benefit $b$, cost $c$) or a public goods game (group size $n$, multiplication factor $r$, cost $c$). In both games the payoff difference $\Pi_C(i)-\Pi_D(i)=\delta<0$ does not depend on the number $i$ of cooperators: $\delta=-(c+\frac{b}{N-1})$ for the donation game and $\delta=-c\big(1-\frac{r(N-n)}{n(N-1)}\big)$ for the public goods game. An institution raises each cooperator's payoff by $\theta$ (reward) or lowers each defector's payoff by $\theta$ (punishment), paying $\theta$ per incentivized individual per generation. Strategies update by the pairwise-comparison (Fermi) rule with selection intensity $\beta$, giving a birth–death chain on $\{0,\dots,N\}$ with transition probabilities $u_{i,i\pm1}=\frac{i(N-i)}{N^2}\big(1+e^{\mp\beta(\delta+\theta)}\big)^{-1}$. With $\mathcal N=(I-U)^{-1}$ the fundamental matrix of the transient states and mutants arising equally from either absorbing state, the expected total cost is

$$
E_r(\theta)=\theta\sum_{i=1}^{N-1}\frac{n_{1i}+n_{N-1,i}}{2}\,i\quad\text{(reward)},\qquad E_p(\theta)=\theta\sum_{i=1}^{N-1}\frac{n_{1i}+n_{N-1,i}}{2}\,(N-i)\quad\text{(punishment)}.
$$

Write $H_N=\sum_{j=1}^{N-1}1/j$.

Let $\theta_0=\frac{1}{(N-1)\beta}\log\frac{\omega}{1-\omega}-\delta$ be the smallest per-capita incentive guaranteeing a desired long-run cooperation frequency $\omega$; the institution minimizes $E(\theta)$ over $\theta\ge\theta_0$.

**Theorem.** Let $F^*=\min\{F(u):P(u)>0\}$ for reward (respectively $\min\{\hat F(u):\hat P(u)>0\}$ for punishment), where $F,P$ (resp. $\hat F,\hat P$) are explicit functions of $u=e^{\beta(\theta+\delta)}$ arising from $E'(\theta)=0$, and set

$$
\beta^*=-\frac{F^*}{\delta}>0.
$$

1. If $\beta\le\beta^*$, $E(\theta)$ is non-decreasing in $\theta$, so $\min_{\theta\ge\theta_0}E(\theta)=E(\theta_0)$.
2. If $\beta>\beta^*$, $E'(\theta)$ changes sign at least twice for every $N$, and exactly twice for $N\le100$: there are $\theta_1<\theta_2$ with $E$ increasing on $(-\infty,\theta_1)$, decreasing on $(\theta_1,\theta_2)$ and increasing on $(\theta_2,\infty)$. Hence for $N\le100$, $\min_{\theta\ge\theta_0}E(\theta)=\min\{E(\theta_0),E(\theta_2)\}$, with $\theta_2=\frac{\log u_2}{\beta}-\delta$ and $u_2$ the largest root of $F(u)+\beta\delta=0$.

For $N=3$ and reward, $F(u)=\frac{(u+1)(5u+4)(u^2+u+1)}{u(4u^2-2u-5)}-\log u$ with $P(u)=4u^2-2u-5$, and $F^*\approx10.93$. The source's Example 4.1 prints the denominator $u(2u^2-u-5/2)$; $u(4u^2-2u-5)$ follows from its displayed $E_r(\theta)$ and reproduces its $F^*\approx10.9291$.

## Expansion

Writing $E'(\theta)=0$ in the variable $u=e^{\beta(\theta+\delta)}$ separates it as $F(u)=-\beta\delta$, so the number of critical points of $E$ equals the number of solutions of a fixed-shape equation with a horizontal line whose height grows with $\beta$. Below the minimum $F^*$ the line misses the graph and $E$ is monotone; above it there are two crossings, the local maximum $\theta_1$ and local minimum $\theta_2$. The phase transition in selection intensity means that under strong selection, paying more per capita can be cheaper in total, because cooperation fixes faster and fewer generations need incentives. The resulting algorithm computes the cost-optimal incentive from $\beta$, $N$, the game parameters and $\omega$.

## Depends on

- [Expected cost of institutional reward and punishment in finite populations](expected-cost-of-institutional-reward-and-punishment-in-finite-populations.md)

## Sources

- Manh Hong Duong, The Anh Han, "Cost efficiency of institutional incentives in finite populations", arXiv:2103.01131: Section 3: Theorem 3.2 (optimization problems and phase transition) and Algorithm 3.3; Section 4: Example 4.1 (N = 3). <https://doi.org/10.48550/arXiv.2103.01131>
