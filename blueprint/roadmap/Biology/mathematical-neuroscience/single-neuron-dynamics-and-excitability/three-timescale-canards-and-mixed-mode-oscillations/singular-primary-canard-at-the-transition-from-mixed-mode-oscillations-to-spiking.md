# Singular primary canard at the transition from mixed-mode oscillations to spiking

**Origin.** A conductance-based model of an entorhinal cortex layer V pyramidal neuron (transient sodium, delayed-rectifier potassium, leak, persistent sodium $I_{Nap}$ and slow potassium $I_{Ks}$) shows mixed-mode oscillations (MMOs): subthreshold oscillations alternating with spikes. Reducing it to the subthreshold regime and truncating gives a three-timescale model system.

**Model system.** For small $\varepsilon > 0$, a control parameter $\mu$ (set by the applied current) and constants $a, b, D_1$ with

$$-b > a > 0 \qquad\text{and}\qquad D_1 < 0,$$

consider

$$\varepsilon^2 \dot x = -y + x^2 + D_1 x^3, \qquad \dot y = x - z, \qquad \varepsilon \dot z = \mu + a x + b z .$$

The critical manifold $S = \{y = x^2 + D_1x^3\}$ has fold lines at $x = 0$ and at the maximum $x_{\max}$ of $x^2 + D_1x^3$; its sheet $S_a = \{x \le 0\}$ is attracting and $S_r = \{0 \le x \le x_{\max}\}$ is repelling. Setting $\varepsilon = 0$ in both the $x$- and $z$-equations gives the super-slow curve

$$S_{1D}:\quad y = x^2 + D_1x^3,\qquad z = -\frac{\mu + a x}{b},$$

along which the flow moves toward the fold (by $-b > a > 0$). For $\varepsilon > 0$ there is a one-dimensional attracting slow manifold $S_{1D,\varepsilon} \subset S_{a,\varepsilon}$ that every spiking trajectory approaches exponentially closely before reaching the fold.

**Fold-region rescaling.** With $x = \varepsilon\bar x$, $y = \varepsilon^2\bar y$, $z = \varepsilon\bar z$, $\mu = \varepsilon\bar\mu$ and $\varepsilon \to 0$, the dynamics near the fold is governed by

$$\bar x' = -\bar y + \bar x^2, \qquad \bar y' = \bar x - \bar z, \qquad \bar z' = \bar\mu + a\bar x + b\bar z. \tag{$\ast$}$$

It has the unique equilibrium $\bar x = \bar z = -\bar\mu/(a+b)$, $\bar y = \bar\mu^2/(a+b)^2$; with $a + b < 0$ its Hopf points are the roots of $C(\bar\mu) = (a+b)a + (2b^2+2)\bar\mu - \frac{4b}{a+b}\bar\mu^2$.

**Results.**
1. *(Special algebraic solution.)* System $(\ast)$ has a polynomial solution exactly when

$$\bar\mu = \bar\mu_0 = -\frac{a(a+b)}{2b^2},$$

namely $\bar x(t) = \bar x_0 + \alpha t$, $\bar y(t) = (\bar x_0 + \alpha t)^2 - \alpha$, $\bar z(t) = (1-2\alpha)(\bar x_0 + \alpha t)$ with $\alpha = (a+b)/(2b)$. It is the unique solution that is algebraic both as $t \to -\infty$ (the continuation of $S_{1D}$ into the fold region) and as $t \to +\infty$ (along the repelling sheet): a singular primary canard.
2. *(MMOs only for $\mu = O(\varepsilon)$.)* There are $L > 0$ and $\varepsilon_0 > 0$ such that for $\varepsilon < \varepsilon_0$ and $\bar\mu > L$ no MMOs exist.
3. *(Transitions through canards.)* If MMO periodic orbits of rotation types $k$ and $k-1$ exist at $\bar\mu_1$ and $\bar\mu_2$, and along $[\bar\mu_1, \bar\mu_2]$ the special solution of $(\ast)$ has only nondegenerate critical points in $\bar x$, then for $\varepsilon$ small the transition between them passes through a canard.
4. *(Limit of canards.)* If $\bar\mu(\varepsilon)$ is continuous and the full rescaled system (with the $\varepsilon D_1\bar x^3$ term) has a primary canard at each $(\bar\mu(\varepsilon), \varepsilon)$, then as $\varepsilon \to 0$ system $(\ast)$ has a singular canard.

The authors conjecture, with numerical evidence, that $\bar\mu_0$ is the $\varepsilon \to 0$ limit of the parameter at which MMOs give way to spiking. Unlike the folded-node mechanism, where canards persist over open parameter ranges, here canards from $S_{1D,\varepsilon}$ to $S_{r,\varepsilon}$ occur only on exponentially small $\bar\mu$-intervals.

## Proof sketch

Fenichel theory gives $S_{a,\varepsilon}$ and $S_{r,\varepsilon}$ away from the folds; the linearization along $S_{1D}$ has two strongly negative eigenvalues $(2x + 3D_1x^2)/\varepsilon^2$ and $b/\varepsilon$, which yields the super-slow attracting curve $S_{1D,\varepsilon}$ and reduces MMO analysis to tracking a single trajectory through the fold. The polynomial solution is found by forcing $\bar x$ linear and $\bar y$ quadratic in $t$ and matching coefficients in the $\bar z$-equation, giving $\alpha - 2\alpha^2 = \bar\mu$ and $a\alpha + b(\alpha - 2\alpha^2) = 0$. A compactification near infinity ($\sigma \sim \bar y^{-1/2}$) and a center-manifold argument show the backward-algebraic solution is unique, so the polynomial solution coincides with it. The bound on $\bar\mu$ uses a trapping tube around $\bar y = \bar x^2$: for large $\bar\mu$ the variable $\bar z$ grows enough that trajectories leave the fold region directly into a relaxation loop, ruling out small oscillations. Neurophysiologically, the persistent sodium and slow potassium currents set the subthreshold oscillations, and the spiking currents set the return; the singular canard marks where small-amplitude rotation is lost.

## Sources

- Jozsi Jalics, Martin Krupa and Horacio G. Rotstein, "Mixed-mode oscillations in a three time-scale system of ODEs motivated by a neuronal model", *Dynamical Systems* 25 (2010), 445–482, <https://doi.org/10.1080/14689360903535760>. Preprint version: arXiv:0804.0829 (2008), Section II (model and reduction) and Section III ("Analysis of mixed-mode oscillations": model system, slow manifolds, the microscope rescaling, the special solution, Proposition 1, Proposition 2 and Theorem 1), <https://doi.org/10.48550/arXiv.0804.0829>.
