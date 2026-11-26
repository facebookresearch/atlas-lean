# Mean-square convergence of Markov processes to their mean-field limits

Let $X_n(t)$ be Markov processes on a bounded convex set $C \subseteq \mathbb{R}^k$ with transition rates $Q_n(x,\hat x)$, and define the first-moment drift and the summed second-moment drift

$$ m_{1,n}(x) = \sum_{\hat x \ne x} Q_n(x,\hat x)(\hat x - x), \qquad m_{2,n}(x) = \sum_{\hat x \ne x} Q_n(x,\hat x)\Big(\sum_i \hat x_i^2 - \sum_i x_i^2\Big), $$

so that $\frac{d}{dt}\mathbb{E}[X_n] = \mathbb{E}[m_{1,n}(X_n)]$ and $\frac{d}{dt}\mathbb{E}[\sum_i X_{n,i}^2] = \mathbb{E}[m_{2,n}(X_n)]$.

**Theorem.** Suppose $X_n(0) \to x_0$ in mean square, $m_{1,n} \to \bar m_1$ and $m_{2,n} \to \bar m_2$ uniformly on $C$, where

$$ \bar m_2(x) = \sum_i 2\, \bar m_{1,i}(x)\, x_i , $$

$\bar m_1$ is Lipschitz, and the Hessians $m''_{1,n}$ and $m''_{2,n}$ are continuous and bounded independently of $n$. Then $X_n(t)$ converges uniformly in mean square on finite time intervals to the solution $\bar x(t)$ of the mean-field equation $x' = \bar m_1(x)$, $x(0) = x_0$:

$$ \sup_{t\le T} \mathbb{E}\big\|X_n(t) - \bar x(t)\big\|^2 \to 0 \qquad \text{for every } T > 0 . $$

For density-dependent processes, where jumps $\Delta_j/n$ occur at rate $n q_j(x)$, one has $m_{1,n} = \sum_j q_j\Delta_j$ for every $n$ and $m_{2,n} = \bar m_2 + O(1/n)$, so the theorem recovers Kurtz's law of large numbers in the stronger mean-square sense; for the stochastic SIS epidemic it gives convergence to $x' = (\beta - \gamma)x - \beta x^2$.

## Depends on

- [Taylor variance bound for moment closure](taylor-variance-bound-for-moment-closure.md)

## Expansion

The condition on $\bar m_2$ says the limit has zero variance: if $\frac{d}{dt}\mathbb{E}\sum_i Y_i^2 = \sum_i 2\,\mathbb{E}[Y_i]'\,\mathbb{E}[Y_i]$ and $Y(0)$ is deterministic, then $\sum_i \mathrm{Var}\,Y_i$ stays zero. Using the Taylor variance bound, $z_n = (\mathbb{E}X_n, \sum_j \mathbb{E}X_{n,j}^2)$ solves an ODE whose right-hand side is $(m_{1,n}, m_{2,n})$ evaluated at the mean plus bounded multiples of $z_2 - \sum_j z_{1,j}^2$ (the total variance). The comparison system with $(\bar m_1, \bar m_2)$ is Lipschitz uniformly in $n$ and has $(\bar x, \sum_j \bar x_j^2)$ as a solution. The standard estimate $\|\phi_1(t) - \phi_2(t)\| \le (\Delta + M/L)e^{Lt} - M/L$ for ODEs with Lipschitz constant $L$, initial gap $\Delta$ and vector-field gap $M$ then shows that first and summed second moments converge, which is mean-square convergence.

## Sources

- B. Armbruster, "A simple and general proof for the convergence of Markov processes to their mean-field limits", arXiv:1602.05224 (2016), Section 1 (Lemma 0 and Theorem 1), Section 2 (proof, Lemma 3) and Section 3 (SIS and heterosexual SI examples). <https://doi.org/10.48550/arXiv.1602.05224>
