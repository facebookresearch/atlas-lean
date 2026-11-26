# Splitting off the first coordinate of the Dirichlet density

Let
$\alpha = (\alpha_0, \dots, \alpha_{n+1}) \in \mathbb{R}^{n+2}$, write $D_\alpha$ for the
unnormalized Dirichlet density with parameters $\alpha$ (a function on $\mathbb{R}^{n+1}$), and let
$\alpha' = (\alpha_1, \dots, \alpha_{n+1}) \in \mathbb{R}^{n+1}$. For every real $t$ with
$0 < t < 1$ and every $u \in \mathbb{R}^n$,

$$D_\alpha(t, (1 - t) u) = t^{\alpha_0 - 1} (1 - t)^{\alpha_1 + \dots + \alpha_{n+1} - 1 - n}
D_{\alpha'}(u)$$

where $(t, (1 - t) u) \in \mathbb{R}^{n+1}$ is the vector with first coordinate $t$ followed by the
coordinates of $(1 - t) u$.
