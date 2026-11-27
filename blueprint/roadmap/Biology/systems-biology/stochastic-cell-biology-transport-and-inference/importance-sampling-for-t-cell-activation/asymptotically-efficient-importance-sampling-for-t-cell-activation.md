# Asymptotically efficient importance sampling for T-cell activation

**T-cell stimulation model.** A T-cell meets an antigen-presenting cell carrying $m$ antigens. A receptor–antigen binding with mean dwell time $\tau$ lasts an $\mathrm{Exp}(1/\tau)$ time and sends a signal only if it lasts at least one time unit, so that antigen contributes the stimulation rate

$$w(\tau) = \frac{1}{\tau}\, e^{-1/\tau},$$

which is maximal at $\tau = 1$ (optimal dwell time). Dwell times $\mathcal{T}_j$ of the different antigen types are random (for instance $\mathrm{Exp}$ with mean $\bar\tau$), and the total stimulation is $G_m = \sum_j z_j\, w(\mathcal{T}_j)$ with antigen copy numbers $z_j$ (constitutive self, variable self, and foreign antigen classes). The T-cell activates when $G_m \ge g_{\mathrm{act}}$; for self-presenting cells this is a rare event whose probability decays exponentially in $m$.

**Importance sampling.** Let $P_n$ be the laws of the normalized sums, with scaled cumulant generating function $\Lambda(\vartheta) = \lim_n n^{-1}\log \mathbb{E}\, e^{n\langle\vartheta, S_n/n\rangle}$, and let $P_n^{\vartheta}$ be the exponentially tilted laws, $dP_n^{\vartheta}/dP_n \propto e^{n\langle\vartheta, x\rangle}$. A family $\{Q_n\}$ is **asymptotically efficient** for a rare event $A$ if the number $N^*_{Q_n}$ of samples needed to reach a fixed relative error grows subexponentially: $n^{-1}\log N^*_{Q_n} \to 0$.

**Proposition.** Suppose $\{P_n\}$ satisfies the hypotheses of the Gärtner–Ellis theorem with good rate function $I = \Lambda^*$, the rare event $A$ has a dominating point $a$, and $\vartheta^*$ is the unique solution of $\nabla\Lambda(\vartheta) = a$; assume moreover the moment condition $\limsup_n n^{-1}\log \mathbb{E}\, e^{\gamma n\langle\pm\vartheta^*, S_n/n\rangle} < \infty$ for some $\gamma > 1$, and that $A$ is a continuity set for $I$ and for $I + \langle\vartheta^*, \cdot\rangle$. Then $\{P_n^{\vartheta^*}\}$ is the **unique** exponentially tilted family that is asymptotically efficient for estimating $P_n(A)$. The normalized T-cell stimulation sums (independent, non-identically distributed summands over the antigen classes) satisfy these hypotheses.

**Tilting through a transformation.** If $Y = h(X)$ and $X$ is tilted by $d\tilde\mu^{\vartheta}/d\mu(x) \propto e^{\langle\vartheta, h(x)\rangle}$, then $h(\tilde X^{\vartheta})$ has exactly the $\vartheta$-tilted law of $Y$. Hence the tilted stimulation rates $w(\mathcal{T})$ can be sampled by drawing dwell times from the explicitly tilted densities $\propto e^{\vartheta z\, w(\tau)}\, f(\tau)$, avoiding the singular density of $W = w(\mathcal{T})$.

## Expansion

By the Dieker–Mandjes criterion, a tilted family $P_n^{\vartheta}$ is asymptotically efficient iff the second-moment exponent of the likelihood-ratio estimator equals twice the decay rate, which reduces to $\inf_x[I(x) - \langle\vartheta, x\rangle] + \inf_{x \in A}[I(x) + \langle\vartheta, x\rangle] = 2\inf_{x\in A} I(x)$. Convex duality gives $\inf_x[I(x) - \langle\vartheta^*, x\rangle] = -\Lambda(\vartheta^*) = I(a) - \langle\vartheta^*, a\rangle$, and the dominating-point property gives $\inf_{A}[I + \langle\vartheta^*, \cdot\rangle] = I(a) + \langle\vartheta^*, a\rangle$; any other $\vartheta$ makes the identity strict and the sample size exponential. In the T-cell model $\vartheta^*$ solves a one-dimensional equation equating $g_{\mathrm{act}}/m$ with the class-weighted tilted means of $w(\mathcal{T})$, computed from the moment-generating function $\psi(t) = \bar\tau^{-1}\int_0^\infty \exp\big(t\, e^{-1/\tau}/\tau - \tau/\bar\tau\big)\, d\tau$; the tilted sampler then estimates activation probabilities of order $10^{-10}$ and smaller with modest sample sizes.

## Sources

- Florian Lipsmeier, Ellen Baake, "Rare Event Simulation for T-cell Activation", Journal of Statistical Physics 134 (2009), 537–566, <https://doi.org/10.1007/s10955-008-9672-2>. Published version of arXiv:0901.2227, cited next; locators there refer to the arXiv version.
- Florian Lipsmeier, Ellen Baake, "Rare event simulation for T-cell activation", arXiv (2009). Definitions 1–2, Theorems 1–3, Proposition 1, Lemmas 1–2, Algorithm 1. <https://doi.org/10.48550/arXiv.0901.2227>
