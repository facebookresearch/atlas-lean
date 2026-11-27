# Predation cross-covariance in chemical Langevin predator–prey models

**Setting.** Prey density $N$ and predator density $P$ on $D=(0,\infty)^2$ change through demographic events $k$ with intensities $f_k(x)$ and stoichiometric jumps $\nu_k\in\mathbb R^2$, in a system of size $\Omega$. The diffusion (chemical Langevin) approximation has drift and covariance

$$b(x)=\sum_kf_k(x)\nu_k,\qquad a(x)=\frac1\Omega\sum_kf_k(x)\,\nu_k\nu_k^{\mathsf T},$$

so the drift sees only first stoichiometric moments while the covariance sees second moments. Predation has Holling type II intensity $f_{\rm pred}(x)=\frac{mNP}{1+N}$ and conversion efficiency $e\in(0,1]$.

**Proposition 5.1 (structural cross-covariance).** The predation contribution to the off-diagonal covariance is
1. under the exact Bernoulli-coupled closure (each predation event removes one prey and, with probability $e$, adds one predator): $\big(a^{(B)}_{\rm pred}\big)_{12}=-\frac1\Omega\,e\,f_{\rm pred}(x)<0$;
2. under the effective coupled closure with jump $(-1,e)$: $\big(a^{(\rm eff)}_{\rm pred}\big)_{12}=-\frac1\Omega\,e\,f_{\rm pred}(x)<0$;
3. under the split-channel closure (independent prey-loss and predator-gain channels with the same drift): $\big(a^{(S)}_{\rm pred}\big)_{12}=0$.

Drift equivalence therefore does not imply covariance equivalence: the sign and presence of predator–prey cross-covariance is decided by whether prey loss and predator gain happen in the same event.

**Theorem 7.1 and Proposition 7.2 (well-posedness).** Consider $dX=b(X)\,dt+\Sigma(X)\,dW$ with $\Sigma\Sigma^{\mathsf T}=a$ and generator $LV=\nabla V\cdot b+\tfrac12\operatorname{tr}(a\nabla^2V)$. Assume

- (A1) on every precompact $K\Subset D$ the coefficients $b$ and $\Sigma$ are Lipschitz and bounded;
- (A2) there are $V_\infty\in C^2(D;[0,\infty))$ and $C>0$ with $LV_\infty\le C(1+V_\infty)$ on $D$ and $V_\infty(x)\to\infty$ as $\|x\|\to\infty$ in $D$.

Then from every $x_0\in D$ there is a unique maximal strong solution with lifetime $\tau^*\in(0,\infty]$, and $\mathbb P(\tau^*<\infty,\ \tau^*<\tau_{\partial D})=0$: if the lifetime is finite, the solution reaches (or approaches) $\partial D$ at $\tau^*$. Without (A2) this fails: $dN=N^2\,dt$, $dP=0$ has locally Lipschitz coefficients but explodes at $t=1$ from $(N_0,P_0)=(1,1)$ inside $D$. If moreover there is $V_b\in C^2(D;[0,\infty))$ with

- (B1) $V_b(x)\to\infty$ as $x\to\partial D$ within $D$, and
- (B2) $LV_b\le C_b(1+V_b)$ on every set $K_n$ of an exhaustion of $D$ by compacts, with one constant $C_b>0$ for all $n$,

then $\mathbb P(\tau_{\partial D}<\infty)=0$, so the solution is global and stays in $D$ for all time.

## Expansion

For the Bernoulli closure the jump is $(-1,1)$ with probability $e$ and $(-1,0)$ with probability $1-e$, so $\mathbb E[\nu_1\nu_2]=-e$; for the effective jump $(-1,e)$ the product is $-e$ deterministically; for split channels each jump has a zero coordinate, so every product $\nu_1\nu_2$ vanishes. A diagonal-noise model, as used when noise is added species by species to the Rosenzweig–MacArthur ODE, thus corresponds to the split-channel representation and discards a correlation that is a stoichiometric consequence of predation–conversion. The negative correlation tilts the fluctuation ellipses, which can change quantities sensitive to joint fluctuations such as extinction risk and the spread of predator–prey cycles.

## Sources

- J. Yu, L. S. Wang, "Beyond Diagonal Noise: A Better Predator-Prey Modeling Framework with Cross-Covariance", *PLOS One* 21(5) (2026), e0350127, Proposition 5.1, Theorem 7.1 and Proposition 7.2, <https://doi.org/10.1371/journal.pone.0350127> (preprint arXiv:2602.22489).
