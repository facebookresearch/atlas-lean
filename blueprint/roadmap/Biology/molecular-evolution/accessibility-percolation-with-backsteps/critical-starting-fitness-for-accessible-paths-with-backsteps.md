# Critical starting fitness for accessible paths with backsteps

In the **House-of-Cards** landscape on the hypercube $\{0,1\}^L$, every site carries an independent fitness uniform on $[0,1]$; the population starts at $\sigma_0 = 00\cdots0$ with fitness $x$, and the fittest site $\sigma_{\mathrm{end}}$ has $H$ coordinates equal to $1$. A path along hypercube edges is **open** (selectively accessible) if fitness strictly increases along it. Unlike shortest-path accessibility, mutations may flip $1 \to 0$ as well as $0 \to 1$ (backsteps), so open paths are self-avoiding paths of any length. Let $\Theta$ be the number of open paths from $\sigma_0$ to $\sigma_{\mathrm{end}}$, and $\mathbb E^x$, $\mathbb P^x$ condition on the starting fitness.

**Theorem.**

1. (*Antipodal target.*) If $H = L$, then $\big[\mathbb E^x(\Theta)\big]^{1/L} \to \sinh(1-x)$ as $L \to \infty$. With $x_1^* = 1 - \operatorname{arcsinh}(1) = 1 - \ln(\sqrt2+1) \approx 0.11863$, $\mathbb E^x(\Theta) \to 0$ exponentially fast (so $\mathbb P^x(\Theta \ge 1) \to 0$) for $x > x_1^*$, and $\mathbb E^x(\Theta)$ diverges exponentially for $x < x_1^*$. Hence $\limsup_L \mathbb P(\Theta \ge 1) \le x_1^*$. Moreover $\mathbb E^x(\Theta) \le L\,\sinh(1-x)^L\coth(1-x)$.
2. (*Target at distance $H \sim \alpha L$.*) If $H(L)/L \to \alpha \in [0,1]$, then

$$\big[\mathbb E^x(\Theta)\big]^{1/L} \to \sinh(1-x)^{\alpha}\cosh(1-x)^{1-\alpha},$$

and the critical fitness $x_\alpha^*$ is the unique solution of $\sinh(1-x_\alpha^*)^{\alpha}\cosh(1-x_\alpha^*)^{1-\alpha} = 1$, with the same dichotomy and $\limsup_L \mathbb P(\Theta \ge 1) \le x_\alpha^*$.
3. (*Random fittest site.*) If the fittest site is uniform on the hypercube, then $\mathbb P^x(\Theta \ge 1) \to 0$ for $x > x_{1/2}^*$, where $x_{1/2}^* = 1 - \tfrac12\operatorname{arcsinh}(2) \approx 0.27818$, so $\lim_L \mathbb P(\Theta \ge 1) \le x_{1/2}^*$.

The authors conjecture that $\mathbb P^x(\Theta \ge 1) \to 1$ below each threshold, which would make $x_\alpha^*$ the exact limiting probability of accessibility.

## Expansion

Given the starting fitness, a fixed self-avoiding path is open with probability equal to the chance that the i.i.d. fitnesses along it exceed $x$ and appear in increasing order, which decays factorially in the path length. Summing over paths, the expected number of open paths is controlled by a generating function $G_L$ of path counts weighted by $X^n/n!$ and evaluated at $X = 1 - x$. For the antipodal target each coordinate must flip an odd number of times, and the paper shows $G_L(X) = \sinh(X)^L$ for the relaxed count, which gives the upper bound; a matching lower bound shows that self-avoidance does not change the exponential rate. For a target with $H$ ones, the $H$ coordinates flipped an odd number of times contribute $\sinh$ and the other $L - H$ (flipped an even number of times) contribute $\cosh$, so $G_{L,H}(X) = \sinh(X)^H\cosh(X)^{L-H}$. A uniform target has $H \approx L/2$, giving $\sinh(X)^{1/2}\cosh(X)^{1/2} = (\tfrac12\sinh 2X)^{1/2}$ and the threshold $\sinh(2(1-x)) = 2$.

## Depends on

- [Number of self-avoiding paths between opposite corners of the hypercube](self-avoiding-paths-between-opposite-corners-of-the-hypercube.md)

## Sources

- Julien Berestycki, Éric Brunet, Zhan Shi, "Accessibility percolation with backsteps", *ALEA Latin American Journal of Probability and Mathematical Statistics* 14 (2017), <https://doi.org/10.30757/ALEA.v14-04>; preprint arXiv:1401.6894, <https://doi.org/10.48550/arXiv.1401.6894>. Numbering of the arXiv version: Section 1 (Theorems 1–3, Conjectures 1–2), Section 2 (Lemmas 1–2), Sections 4–5.
