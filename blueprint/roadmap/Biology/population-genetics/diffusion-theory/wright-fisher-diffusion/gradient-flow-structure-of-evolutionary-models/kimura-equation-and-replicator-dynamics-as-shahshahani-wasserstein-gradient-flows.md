# Kimura equation and replicator dynamics as Shahshahani–Wasserstein gradient flows

**Setting.** For two types with frequency $x \in [0,1]$, let $\Theta(x) = x(1-x)$ (more generally a coefficient vanishing linearly at $0$ and $1$) and let $V$ be the fitness potential. The **Kimura equation**, the diffusion limit of the Moran process with diffusion coefficient $\kappa > 0$, is

$$ \partial_t p = \frac{\kappa}{2}\partial^2_{xx}\big(\Theta p\big) + \partial_x\big(\Theta\,\partial_xV\,p\big), \qquad t > 0,\ x \in [0,1], $$

and the **replicator equation** is its deterministic limit $\dot X = -\Theta(X)\,V'(X)$. Equip $(0,1)$ with the Riemannian metric $|\zeta|^2_{T_x} = |\zeta|^2/\Theta(x)$. Its geodesic distance $\mathsf{d}$ is the (generalized) Shahshahani distance, and it induces a quadratic Wasserstein distance $W_{\mathsf d}$ on $\mathcal{P}([0,1])$.

**Theorem (Kimura equation).** Let $p = a\,\delta_0 + \widetilde p + b\,\delta_1$, where $\widetilde p$ is the absolutely continuous (non-fixed) part. Let $w$ be the principal eigenfunction of the backward operator with Dirichlet conditions, $\mathcal{L}^\dagger w = -\lambda w$, $w(0) = w(1) = 0$, so that $\langle w,\widetilde p(t)\rangle = e^{-\lambda t}\langle w,\widetilde p(0)\rangle$. For non-absorbed initial data, the conditioned density $q = w\widetilde p/\langle w,\widetilde p\rangle$ (the law of the Q-process) solves

$$ \partial_t q = \partial_x\Big(\Theta\,q\,\partial_x\Big(\frac{\kappa}{2}\log\frac{q}{\pi}\Big)\Big), \qquad \pi = \frac{1}{C}\frac{w^2e^{-2V/\kappa}}{\Theta}, $$

that is, $q$ is the $W_{\mathsf d}$-gradient flow of the relative entropy $\frac{\kappa}{2}\int q\log(q/\pi)$. The no-flux condition for $q$ is equivalent to the Dirichlet condition $q(0) = q(1) = 0$, and $p$ is recovered from $q$.

**Theorem (replicator dynamics).** The minimizing-movement (JKO) scheme

$$ X^{n+1} \in \operatorname*{arg\,min}_{X \in [0,1]}\Big\{ \frac{1}{2h}\mathsf{d}(X,X^n)^2 + V(X) \Big\}, \qquad X^0 = X^I, $$

has piecewise-constant interpolants $X_h$ that converge uniformly on every $[0,T]$, as $h \to 0$, to the unique solution of $\dot X = -\Theta(X)V'(X)$, $X(0) = X^I$. The replicator equation is thus the gradient flow of $V$ for the Shahshahani metric.

Section 6 argues, without a complete proof, that these structures are compatible in the limits $N\to\infty$ and $\kappa\to0$: it proves $\Gamma$-convergence of the driving entropies, $H(\cdot\mid\pi_N)\to H(\cdot\mid\pi)$ when $\pi_N\rightharpoonup\pi$ (Lemma 11), and $\frac{\kappa}{2}\int q\log(q/\pi_\kappa)\to\int V\,dq$ (up to $\min V$) when $\pi_\kappa$ satisfies a large deviation principle with rate $V$ (Proposition 3).

## Depends on

- [Gradient-flow structure of absorbing evolutionary Markov chains via the Q-process](gradient-flow-structure-of-absorbing-evolutionary-markov-chains-via-the-q-process.md)
- [Backward generator of the Wright–Fisher diffusion with selection](../generator.md)

## Proof depends on

## Expansion

The degenerate diffusion $\Theta(x) = x(1-x)$ makes Euclidean optimal transport the wrong geometry. Rescaling space by the metric $dx^2/\Theta$ turns the Kimura operator into a Fokker–Planck operator, and Otto's formula $\operatorname{grad}_{W}\mathcal{F} = -\partial_x\big(\Theta q\,\partial_x\frac{\delta\mathcal{F}}{\delta q}\big)$ identifies the conditioned dynamics with entropy dissipation. Fixation at $0$ and $1$ is removed by the same Doob transform with the Dirichlet eigenfunction $w$ that handles the discrete Moran chain. As $\kappa \to 0$ the entropy term vanishes, measures concentrate on points, and $W_{\mathsf d}$ restricted to Dirac masses is $\mathsf{d}$, which yields the Shahshahani gradient flow.

## Sources

- Fabio A. C. C. Chalub, Léonard Monsaingeon, Ana Margarida Ribeiro and Max O. Souza, "Gradient flow formulations of discrete and continuous evolutionary models: a unifying perspective", arXiv:1907.01681 (2019), Section 4 (Kimura equation, Wasserstein distance and gradient flow formulation), Section 5 (replicator dynamics), Section 6 (Theorem 4 and Γ-convergence results), <https://doi.org/10.48550/arXiv.1907.01681>; published in *Acta Applicandae Mathematicae* 171 (2021), article 24, <https://doi.org/10.1007/s10440-021-00391-9>. Locators follow arXiv v2.
