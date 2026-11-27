# Predation cross-covariance in chemical Langevin predator–prey models

**Setting.** Prey density $N$ and predator density $P$ on $D=(0,\infty)^2$ change through demographic events $k$ with intensities $f_k(x)$ and stoichiometric jumps $\nu_k\in\mathbb R^2$, in a system of size $\Omega$. The diffusion (chemical Langevin) approximation has drift and covariance

$$b(x)=\sum_kf_k(x)\nu_k,\qquad a(x)=\frac1\Omega\sum_kf_k(x)\,\nu_k\nu_k^{\mathsf T},$$

so the drift sees only first stoichiometric moments while the covariance sees second moments. Predation has Holling type II intensity $f_{\rm pred}(x)=\frac{mNP}{1+N}$ and conversion efficiency $e\in(0,1]$.

**Proposition 5.1 (structural cross-covariance).** The predation contribution to the off-diagonal covariance is
1. under the exact Bernoulli-coupled closure (each predation event removes one prey and, with probability $e$, adds one predator): $\big(a^{(B)}_{\rm pred}\big)_{12}=-\frac1\Omega\,e\,f_{\rm pred}(x)<0$;
2. under the effective coupled closure with jump $(-1,e)$: $\big(a^{(\rm eff)}_{\rm pred}\big)_{12}=-\frac1\Omega\,e\,f_{\rm pred}(x)<0$;
3. under the split-channel closure (independent prey-loss and predator-gain channels with the same drift): $\big(a^{(S)}_{\rm pred}\big)_{12}=0$.

Drift equivalence therefore does not imply covariance equivalence: the sign and presence of predator–prey cross-covariance is decided by whether prey loss and predator gain happen in the same event.

**Theorem 7.1 and Proposition 7.2 (well-posedness).** If the drift and diffusion coefficients are locally Lipschitz on compacts of $D$, the SDE $dX=b(X)\,dt+\sigma(X)\,dW$ with $\sigma\sigma^{\mathsf T}=a$ has a unique maximal strong solution that cannot explode in the interior before reaching the boundary of $D$; if in addition a $C^2$ barrier function $V_b$ blowing up at $\partial D$ satisfies a Lyapunov drift bound, the solution stays in $D$ for all time.

## Expansion

For the Bernoulli closure the jump is $(-1,1)$ with probability $e$ and $(-1,0)$ with probability $1-e$, so $\mathbb E[\nu_1\nu_2]=-e$; for the effective jump $(-1,e)$ the product is $-e$ deterministically; for split channels each jump has a zero coordinate, so every product $\nu_1\nu_2$ vanishes. A diagonal-noise model, as used when noise is added species by species to the Rosenzweig–MacArthur ODE, thus corresponds to the split-channel representation and discards a correlation that is a stoichiometric consequence of predation–conversion. The negative correlation tilts the fluctuation ellipses, which can change quantities sensitive to joint fluctuations such as extinction risk and the spread of predator–prey cycles.

## Sources

- J. Yu, L. S. Wang, "Beyond Diagonal Noise: A Better Predator-Prey Modeling Framework with Cross-Covariance", *PLOS One* 21(5) (2026), e0350127, Proposition 5.1, Theorem 7.1 and Proposition 7.2, <https://doi.org/10.1371/journal.pone.0350127> (preprint arXiv:2602.22489).
