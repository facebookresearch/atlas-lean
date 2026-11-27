# A fourth-root Berry–Esseen bound for non-identical summands

Let $X_1, \dots, X_n$ be independent real random variables in $L^3$ with $\mathbb{E}X_i = 0$ and $\sum_i \mathbb{E}X_i^2 = 1$, and let $\gamma = \sum_i \mathbb{E}|X_i|^3$. Then for every $u \in \mathbb{R}$,

$$\Big|\Pr\Big[\sum_i X_i \le u\Big] - \Phi(u)\Big| \le c\,\gamma^{1/4},$$

where $\Phi$ is the standard Gaussian distribution function and $c$ is a universal constant (O'Donnell, Cor. 11.62). (The classical Berry–Esseen theorem improves $\gamma^{1/4}$ to $O(\gamma)$.)

## Proof sketch

Compare with independent Gaussians $Y_i \sim N(0, \mathbb{E}X_i^2)$, whose sum is standard Gaussian, via the Lévy-distance invariance bound; $\mathbb{E}|Y_i|^3 \le 2\mathbb{E}|X_i|^3$ by Lyapunov's inequality, and the Gaussian density is bounded so Lévy closeness gives Kolmogorov closeness.

## Depends on

- [Lévy distance and the hypothesis of the basic invariance principle](levy-distance-and-invariance-hypothesis.md)

## Proof depends on

- [Invariance principle for sums of independent random variables](invariance-principle-for-sums.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
