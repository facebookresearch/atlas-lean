# Rao–Blackwell risk decomposition for a discrete sufficient statistic

Let $X$ be a finite set and $\mathcal{T}$ a set, both with the discrete σ-algebra, let $(p_\theta)_{\theta \in \Theta}$ be probability mass functions on $X$ with probability measures $P_\theta$, and let $T : X \to \mathcal{T}$ be a statistic that is [sufficient for the discrete family](is-sufficient-pmf.md) $(p_\theta)$. Let $W : X \to \mathbb{R}$ satisfy $\mathbb{E}_{P_\theta}[W^2] < \infty$ for every $\theta$, and let $\tau : \Theta \to \mathbb{R}$. Then there is a measurable $\varphi : \mathcal{T} \to \mathbb{R}$ such that for every $\theta$

$$\mathbb{E}_{P_\theta}\big[(W - \tau(\theta))^2\big] = \mathbb{E}_{P_\theta}\big[(\varphi(T) - \tau(\theta))^2\big] + \mathbb{E}_{P_\theta}\big[(W - \varphi(T))^2\big].$$

In particular the mean squared error of $\varphi(T)$ is at most that of $W$, for every parameter.
