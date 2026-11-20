# Sharpness of the phase transition, conditional form

Let $d \in \mathbb{N}$. For Bernoulli bond percolation on $\mathbb{Z}^d$ write $\theta(p)$ for the [percolation probability](../../phase-transition/percolation-probability-and-critical-point/theta.md), $\theta_n(p) = \mathbb{P}_p(0 \leftrightarrow \mathbb{Z}^d \setminus \Lambda_{n-1})$ for the [one-arm probability](cross-prob-real.md) (extended by $0$ outside $[0, 1]$), $\tilde p_c = \tilde p_c(d)$ for the [Duminil-Copin–Tassion threshold](../the-duminil-copin-tassion-quantity-p-s-and-the-t/tilde-pc.md) and $\tilde{\mathcal{S}}$ for the [set of densities defining it](../the-duminil-copin-tassion-quantity-p-s-and-the-t/tilde-pc-set.md). Assume:

1. $\tilde p_c > 0$ and $\theta(1) \ne 0$;
2. (exponential decay) for every $p \in \tilde{\mathcal{S}}$ there are $c, C > 0$ with $\theta_n(p) \le C e^{-cn}$ for all $n \in \mathbb{N}$;
3. (differential inequality) there are functions $F'_{n, q} : \mathbb{R} \to \mathbb{R}$ such that for every $q$ with $\tilde p_c < q < 1$ and every $n \in \mathbb{N}$, the function $\theta_{n+1}$ is continuous on $[\tilde p_c, q]$, has derivative $F'_{n, q}(t)$ at every $t \in (\tilde p_c, q)$, and $F'_{n, q}(t) \ge \dfrac{1 - \theta_{n+1}(t)}{t(1 - t)}$ for all $t \in (\tilde p_c, q)$.

Then:

- $\tilde p_c = p_c(d)$;
- for every $p \in \tilde{\mathcal{S}}$ there are $c, C > 0$ with $\theta_n(p) \le C e^{-cn}$ for all $n$ (this restates assumption 2);
- for every $q$ with $\tilde p_c < q < 1$,

$$\theta(q) \ge \frac{q - \tilde p_c}{q(1 - \tilde p_c)}.$$

The [sharpness theorem for Bernoulli bond percolation](../sharpness-of-the-phase-transition-for-bernoulli/sharp-phase-transition.md) proves the assumptions.
