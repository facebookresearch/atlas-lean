# Sweep duration and hitchhiking genealogy under dominance

In a diploid Wright–Fisher population of size $N$, a beneficial allele $B$ has genotype fitnesses $BB : Bb : bb = 1+s : 1+sh : 1$ with dominance $h \in [0,1]$. As $N \to \infty$, $s \to 0$ with $2Ns \to \alpha$, its frequency converges to the diffusion

$$dX = \alpha\big(h + X(1-2h)\big)X(1-X)\,dt + \sqrt{X(1-X)}\,dW.$$

Let $X^*$ be this diffusion started at $0$ and conditioned to hit $1$, and $T^*$ its fixation time (the length of the sweep, in diffusion time units). Write $\approx$ for asymptotic equivalence as $\alpha \to \infty$.

**Theorem (recessive sweep, $h = 0$).** Then $dX = \alpha X^2(1-X)\,dt + \sqrt{X(1-X)}\,dW$, a new allele at frequency $\varepsilon_\alpha$ with $\varepsilon_\alpha\sqrt\alpha \to 0$ fixes with probability $\approx 2\varepsilon_\alpha\sqrt{\alpha/\pi}$, and

$$\mathbb E_0[T^*] - \frac{4 c_{\mathrm{cat}}}{\sqrt\pi}\cdot\frac{1}{\sqrt\alpha} \approx \frac{3\log\alpha}{2\alpha}, \qquad \mathrm{Var}_0[T^*] \approx \frac{c}{\alpha},$$

with $c_{\mathrm{cat}} \approx 0.916$ Catalan's constant ($4c_{\mathrm{cat}}/\sqrt\pi \approx 2.067$) and some $0 < c < \infty$. So a recessive sweep lasts of order $\sqrt{N/s}$ generations rather than the $\log(Ns)/s$ of a co-dominant sweep: the allele spends most of the sweep at frequencies of order $1/\sqrt\alpha$, where it is mostly in heterozygotes and nearly invisible to selection, and $\sqrt\alpha\,X^*_{t/\sqrt\alpha}$ converges to the diffusion $dY = Y^2\,dt + \sqrt Y\,dW$.

**Theorem (genealogy, $h = 0$).** In the structured coalescent along the sweep, with recombination rate $\rho$ between the selected and a neutral locus scaled as $\rho/\sqrt\alpha \to \lambda \in (0,\infty)$, a single lineage stays in the beneficial background with probability $\approx \mathbb E_0[e^{-\lambda\sqrt\alpha\,T^*}]$, and a sample of $n$ lineages in the beneficial background ends the sweep with $k$ distinct lineages with probability tending to a constant $c_{\lambda,n,k} \in (0,1)$. Hence linked diversity is affected over a much wider genomic window, of recombination distance order $\sqrt\alpha$, than for co-dominant sweeps, and the reduction does not take the star-like form of a classical sweep.

**Theorem (incomplete and complete dominance).** For $0 < h \le 1$ the fixation probability from $\varepsilon_\alpha$ with $\varepsilon_\alpha\alpha \to 0$ is $\approx 2h\alpha\varepsilon_\alpha$ (about $2hs$ for a single copy). For $0 < h < 1$,

$$\mathbb E_0[T^*] = \frac{\log(2\alpha) + \gamma + (2-3h)\log h + (3h-1)\log(1-h)}{\alpha h(1-h)} + o(\alpha^{-1}), \qquad \mathrm{Var}_0[T^*] \approx \frac{1}{\alpha^2}\Big(\frac{c'}{h^2} + \frac{c''}{(1-h)^2}\Big),$$

with $\gamma$ Euler's constant; for $h = 1$, $\mathbb E_0[T^*] - \pi^{3/2}/(2\sqrt\alpha) \approx 3\log\alpha/(2\alpha)$. Diversity patterns for $0 < h < 1$ match those of a co-dominant sweep with selection coefficient $2hs$.

## Depends on

- [Fixation probability of a recessive allele](../../population-genetics/diffusion-theory/selection-and-dominance-in-kimura-s-fixation-pro/fixation-prob-dominance-zero-h.md)

## Expansion

The conditioned diffusion $X^*$ has drift $\alpha(h + X(1-2h))X(1-X) + X(1-X)\,\partial_x\log\mathbb P_x[T_1 < T_0]$. For $h > 0$ the drift near $0$ is linear, $\approx \alpha h X$, so the sweep splits into a logistic-like middle phase and two boundary phases of length $\log\alpha/(\alpha h)$ and $\log\alpha/(\alpha(1-h))$, which produce the $1/(h(1-h))$ prefactor. For $h = 0$ the drift near $0$ is quadratic, and under the scaling $Y_t = \sqrt\alpha\,X_{t/\sqrt\alpha}$ the dynamics converge to $dY = Y^2\,dt + \sqrt Y\,dW$ conditioned to explode; the expected explosion time evaluates to $4c_{\mathrm{cat}}/\sqrt\pi$ through an explicit Green-function integral, giving the $1/\sqrt\alpha$ leading term. The structured coalescent result follows because the lineages spend time of order $1/\sqrt\alpha$ at frequencies of order $1/\sqrt\alpha$, during which both coalescence (rate inversely proportional to frequency) and recombination at rate $\rho = \lambda\sqrt\alpha$ act on comparable scales.

## Sources

- Greg Ewing, Joachim Hermisson, Peter Pfaffelhuber, Johannes Rudolf, "Selective sweeps for recessive alleles and for other modes of dominance", *Journal of Mathematical Biology* 63 (2011), 399–431, <https://doi.org/10.1007/s00285-010-0382-4>; preprint arXiv:1005.5536, <https://doi.org/10.48550/arXiv.1005.5536>. Numbering of the arXiv version: Section 2 (Wright–Fisher model and diffusion limit, structured coalescent), Section 3 (Proposition 1, Theorems 1 and 2 with remarks), Section 4 (Proposition 2, Theorem 3), Section 7 (Key lemma on the rescaled diffusion).
