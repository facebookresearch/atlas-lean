# Expected cost of institutional reward and punishment in finite populations

**Model.** A well-mixed population of $N$ players, cooperators (C) and defectors (D), plays the donation game (benefit $b$, cost $c$) or a public goods game (group size $n$, multiplication factor $r$, cost $c$). In both games the payoff difference $\Pi_C(i)-\Pi_D(i)=\delta<0$ does not depend on the number $i$ of cooperators: $\delta=-(c+\frac{b}{N-1})$ for the donation game and $\delta=-c\big(1-\frac{r(N-n)}{n(N-1)}\big)$ for the public goods game. An institution raises each cooperator's payoff by $\theta$ (reward) or lowers each defector's payoff by $\theta$ (punishment), paying $\theta$ per incentivized individual per generation. Strategies update by the pairwise-comparison (Fermi) rule with selection intensity $\beta$, giving a birth–death chain on $\{0,\dots,N\}$ with transition probabilities $u_{i,i\pm1}=\frac{i(N-i)}{N^2}\big(1+e^{\mp\beta(\delta+\theta)}\big)^{-1}$. With $\mathcal N=(I-U)^{-1}$ the fundamental matrix of the transient states and mutants arising equally from either absorbing state, the expected total cost is

$$
E_r(\theta)=\theta\sum_{i=1}^{N-1}\frac{n_{1i}+n_{N-1,i}}{2}\,i\quad\text{(reward)},\qquad E_p(\theta)=\theta\sum_{i=1}^{N-1}\frac{n_{1i}+n_{N-1,i}}{2}\,(N-i)\quad\text{(punishment)}.
$$

Write $H_N=\sum_{j=1}^{N-1}1/j$.

**Theorem.** For both reward and punishment:
1. $\theta\mapsto E(\theta)$ is smooth on $\mathbb R$.
2. For every finite $N$,

$$
\frac{N^2\theta}{2}\Big(H_N+\frac{1}{N-1}\Big)\le E(\theta)\le N(N-1)\theta\,(H_N+1).
$$

3. As $N\to\infty$, $E(\theta)\big/\big(\tfrac{N^2\theta}{2}(\ln N+\gamma)\big)\to1+e^{-\beta|\theta-c|}$ for the donation game and $\to1+e^{-\beta|\theta-c(1-r/n)|}$ for the public goods game, where $\gamma$ is the Euler–Mascheroni constant. The source (arXiv:2103.01131, Theorem 3.1(3), eq. (11)) prints $1+e^{-\beta|\theta-c|}e^{\beta cr/n}$ for the public goods game, which agrees with this only for $\theta\le c(1-r/n)$; the form above follows from $\lim_{N\to\infty}e^{\beta(\theta+\delta)}=e^{\beta(\theta-c(1-r/n))}$ in its proof of Proposition 1.11.
4. In the weak-selection limit, $\lim_{\beta\to0}E(\theta)=N^2\theta H_N$.

## Expansion

The chain is a birth–death process whose ratio of down- to up-moves is $e^{-\beta(\delta+\theta)}$ in every state, so the fundamental matrix has explicit entries in terms of geometric sums of $x=e^{\beta(\delta+\theta)}$, and $E(\theta)$ is $\theta$ times a rational function of $x$. At neutrality ($\beta=0$) the Fermi rule moves up or down with probability $\frac{i(N-i)}{2N^2}$ each, so the expected sojourn in state $i$ is $2N/i$ from state $1$ and $2N/(N-i)$ from state $N-1$, and the total is $N^2\theta H_N=N^2\theta\sum_{j=1}^{N-1}1/j$; the harmonic number is the source of the $N^2\ln N$ growth in general. The bounds follow by comparing the expected visit counts with their extreme values at $x\to0$ and $x\to\infty$. Since the cost grows like $N^2\ln N$, incentive schemes become expensive in large populations, motivating the optimization of $\theta$.

## Sources

- Manh Hong Duong, The Anh Han, "Cost efficiency of institutional incentives in finite populations", arXiv:2103.01131: Section 2 (cooperation dilemmas, institutional incentives and cost of incentives); Section 3: Theorem 3.1, parts (1)–(4). <https://doi.org/10.48550/arXiv.2103.01131>
