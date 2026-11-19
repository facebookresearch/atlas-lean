# Domain of attraction

Let $\mu$ and $G$ be measures on $\mathbb{R}$. Then $\mu$ is in the domain of attraction of $G$ if
$\mu$ and $G$ are probability measures and there are sequences $a_n > 0$ and $b_n \in \mathbb{R}$
($n \in \mathbb{N}$) such that for every bounded continuous $f : \mathbb{R} \to \mathbb{R}$,

$$\int f \, d\big(\text{law of } (S_n - b_n)/a_n\big) \to \int f \, dG \qquad (n \to \infty),$$

where $S_n$ has law $\mu^{*n}$, the $n$-fold convolution power of $\mu$ (with
$\mu^{*0} = \delta_0$). That is, the image of $\mu^{*n}$ under $y \mapsto (y - b_n)/a_n$ converges
weakly to $G$.
