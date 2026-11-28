# Kimura equation and replicator dynamics as Shahshahani–Wasserstein gradient flows

**Setting.** For two types with frequency $x \in [0,1]$, let $\Theta(x) = x(1-x)$ (more generally a smooth coefficient $\Theta \in C^k([0, 1])$ ($k \ge 2$) positive on $(0, 1)$ with simple zeros at $0$ and $1$, $\partial_x\Theta(0) > 0$ and $\partial_x\Theta(1) < 0$ (the source's (36))) and let $V:[0,1]\to\mathbb R$ be the fitness potential, assumed smooth up to the boundary, as throughout the source (its well-posedness and regularity results take $\Theta,V\in C^k([0,1])$, and its JKO convergence theorem rests on "our smoothness assumptions on the potential $V$"). The **Kimura equation**, the diffusion limit of the Moran process with diffusion coefficient $\kappa > 0$, is

$$ \partial_t p = \frac{\kappa}{2}\partial^2_{xx}\big(\Theta p\big) + \partial_x\big(\Theta\,\partial_xV\,p\big), \qquad t > 0,\ x \in [0,1], $$

and the **replicator equation** is its deterministic limit $\dot X = -\Theta(X)\,V'(X)$. Equip $(0,1)$ with the Riemannian metric $|\zeta|^2_{T_x} = |\zeta|^2/\Theta(x)$. Its geodesic distance $\mathsf{d}$ is the (generalized) Shahshahani distance, and it induces a quadratic Wasserstein distance $W_{\mathsf d}$ on $\mathcal{P}([0,1])$.

**Theorem (Kimura equation).** Let $p = a\,\delta_0 + \widetilde p + b\,\delta_1$, where $\widetilde p$ is the absolutely continuous (non-fixed) part. Let $w$ be the principal eigenfunction of the backward operator with Dirichlet conditions, $\mathcal{L}^\dagger w = -\lambda w$, $w(0) = w(1) = 0$, so that $\langle w,\widetilde p(t)\rangle = e^{-\lambda t}\langle w,\widetilde p(0)\rangle$. For non-absorbed initial data, the conditioned density $q = w\widetilde p/\langle w,\widetilde p\rangle$ (the law of the Q-process) solves

$$ \partial_t q = \partial_x\Big(\Theta\,q\,\partial_x\Big(\frac{\kappa}{2}\log\frac{q}{\pi}\Big)\Big), \qquad \pi = \frac{1}{C}\frac{w^2e^{-2V/\kappa}}{\Theta}, $$

that is, $q$ is the $W_{\mathsf d}$-gradient flow of the relative entropy $\frac{\kappa}{2}\int q\log(q/\pi)$. The no-flux condition for $q$ is equivalent to the Dirichlet condition $q(0) = q(1) = 0$, and $p$ is recovered from $q$.

**Theorem (replicator dynamics).** The minimizing-movement (JKO) scheme

$$ X^{n+1} \in \operatorname*{arg\,min}_{X \in [0,1]}\Big\{ \frac{1}{2h}\mathsf{d}(X,X^n)^2 + V(X) \Big\}, \qquad X^0 = X^I, $$

has piecewise-constant interpolants $X_h$ that converge uniformly on every $[0,T]$, as $h \to 0$, to the unique solution of $\dot X = -\Theta(X)V'(X)$, $X(0) = X^I$. The replicator equation is thus the gradient flow of $V$ for the Shahshahani metric. The smoothness of $V$ cannot be dropped: for $\Theta(x)=x(1-x)$ and $V(x)=-\frac23|x-\frac12|^{3/2}$, whose derivative $V'(x)=-\operatorname{sgn}(x-\frac12)\,|x-\frac12|^{1/2}$ is not Lipschitz at $\frac12$, the equation $\dot X=\Theta(X)\operatorname{sgn}(X-\frac12)|X-\frac12|^{1/2}$ with $X^I=\frac12$ has the constant solution and also solutions leaving $\frac12$ with $|X(t)-\frac12|\sim t^2/64$, so the limit is not unique; correspondingly the JKO step from $X^0=\frac12$ has two minimizers, both different from $\frac12$, because $-\frac23|y|^{3/2}$ beats the quadratic penalty for small $|y|$.

Section 6 argues, without a complete proof, that these structures are compatible in the limits $N\to\infty$ and $\kappa\to0$: it proves $\Gamma$-convergence of the driving entropies, $H(\cdot\mid\pi_N)\to H(\cdot\mid\pi)$ when $\pi_N\rightharpoonup\pi$ (Lemma 11), and $\frac{\kappa}{2}\int q\log(q/\pi_\kappa)\to\int V\,dq$ (up to $\min V$) when $\pi_\kappa$ satisfies a large deviation principle with speed $2/\kappa$ and rate function $V$ (Proposition 3), that is, $-\inf_{\mathring E}V\le\liminf_{\kappa\to0}\frac{\kappa}{2}\log\pi_\kappa(E)\le\limsup_{\kappa\to0}\frac{\kappa}{2}\log\pi_\kappa(E)\le-\inf_{\overline E}V$ for every Borel set $E\subset[0,1]$. The source notes that this hypothesis must be checked case by case; for $\Theta(x)=x(1-x)$ and $V\equiv0$ (a constant potential normalized by subtracting its minimum), $\pi_\kappa(x)=6x(1-x)$ for every $\kappa$, so (68) holds.

## Depends on

- [Minimizing movement step](../../../../../MeasureTheory/optimal-transport/wasserstein-gradient-flows-and-the-jko-scheme/minimizing-movements/is-minimizing-movement-step.md)
- [Minimizing movement scheme](../../../../../MeasureTheory/optimal-transport/wasserstein-gradient-flows-and-the-jko-scheme/minimizing-movements/is-minimizing-movement.md)
- [Quadratic Wasserstein distance](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein.md)
- [Gradient-flow structure of absorbing evolutionary Markov chains via the Q-process](gradient-flow-structure-of-absorbing-evolutionary-markov-chains-via-the-q-process.md)
- [Backward generator of the Wright–Fisher diffusion with selection](../generator.md)

## Proof depends on

## Expansion

The degenerate diffusion $\Theta(x) = x(1-x)$ makes Euclidean optimal transport the wrong geometry. Rescaling space by the metric $dx^2/\Theta$ turns the Kimura operator into a Fokker–Planck operator, and Otto's formula $\operatorname{grad}_{W}\mathcal{F} = -\partial_x\big(\Theta q\,\partial_x\frac{\delta\mathcal{F}}{\delta q}\big)$ identifies the conditioned dynamics with entropy dissipation. Fixation at $0$ and $1$ is removed by the same Doob transform with the Dirichlet eigenfunction $w$ that handles the discrete Moran chain. As $\kappa \to 0$ the entropy term vanishes, measures concentrate on points, and $W_{\mathsf d}$ restricted to Dirac masses is $\mathsf{d}$, which yields the Shahshahani gradient flow.

## Sources

- Fabio A. C. C. Chalub, Léonard Monsaingeon, Ana Margarida Ribeiro and Max O. Souza, "Gradient flow formulations of discrete and continuous evolutionary models: a unifying perspective", arXiv:1907.01681 (2019), Section 4 (Kimura equation, Wasserstein distance and gradient flow formulation), Section 5 (replicator dynamics), Section 6 (Theorem 4 and Γ-convergence results), <https://doi.org/10.48550/arXiv.1907.01681>; published in *Acta Applicandae Mathematicae* 171 (2021), article 24, <https://doi.org/10.1007/s10440-021-00391-9>. Locators follow arXiv v2.
