# Moran-type bounds for fixation in the frequency-dependent Wright–Fisher process

Two strategies $A$ and $B$ play a symmetric $2\times2$ game with positive payoffs $a$ ($A$ vs $A$), $b$ ($A$ vs $B$), $c$ ($B$ vs $A$), $d$ ($B$ vs $B$). In a population of size $N$ with $i$ individuals of type $A$, fitnesses are $f_N(i)=1-w+w\frac{a(i-1)+b(N-i)}{N-1}$ and $g_N(i)=1-w+w\frac{ci+d(N-i-1)}{N-1}$ with selection parameter $w\in(0,1)$. The Wright–Fisher chain moves from $i$ to $\mathrm{Bin}(N,\xi_N(i))$, where

$$ \xi_N(i)=\frac{i f_N(i)}{i f_N(i)+(N-i)g_N(i)}, $$

and $p_N(i)$ is the probability of absorption at $N$ (fixation of $A$) from $i$. Assume (strong selection for $A$) that there are $N_0\ge2$ and constants $0<\alpha\le\gamma<1$ with $\alpha\le g_N(i)/f_N(i)\le\gamma$ for all $N\ge N_0$ and $1\le i\le N-1$; since $f_N,g_N$ are linear in $i$, this holds when $A$ strictly dominates, $a>c$ and $b>d$.

**Theorem.** With $\rho=e^{-2(1-\gamma)}$ and $\theta=e^{-2(1-\alpha)/\alpha}$,

$$ \frac{1-\rho^i}{1-\rho^N}\le p_N(i)\le\frac{1-\theta^i}{1-\theta^N}\qquad\text{for all }N\ge N_0,\ 1\le i\le N-1. $$

Both bounds have the form of the Moran fixation probability $(1-r^{-i})/(1-r^{-N})$ for a constant fitness ratio, so the frequency-dependent chain is sandwiched between two constant-selection benchmarks. Consequently $\liminf_{N\to\infty}p_N(i)>0$ for each fixed $i$, and $p_N(i_N)\to1$ whenever $i_N\to\infty$. For fixed $N$, $p_N(i)$ is strictly increasing in $i$, and it increases with $w$ and $b$ and decreases with $c$.

## Depends on

- [Fixation probability of the Moran process](../../../../population-genetics/moran-model/moran-fixation.md)

## Expansion

The key step is a one-step exponential-moment inequality: for these $\rho,\theta$, $E[\rho^{X_{t+1}}\mid X_t=i]\le\rho^i$ and $E[\theta^{X_{t+1}}\mid X_t=i]\ge\theta^i$ for every interior $i$, using the binomial generating function $(1-\xi(1-x))^N$ and the bounds on $g_N/f_N$. Hence $\rho^{X_t}$ is a bounded supermartingale and $\theta^{X_t}$ a bounded submartingale. Optional stopping at the absorption time gives $\rho^i\ge p_N(i)\rho^N+1-p_N(i)$ and the reverse inequality for $\theta$, which rearrange to the two bounds. Monotonicity in $i$ comes from a coupling of binomial processes driven by ordered success probabilities.

## Sources

- T. Chumley, O. Aydogmus, A. Matzavinos and A. Roitershtein, "Moran-type bounds for the fixation probability in a frequency-dependent Wright–Fisher model", arXiv:1609.00838 (2016), <https://doi.org/10.48550/arXiv.1609.00838>. Theorem 5 (explicit bounds, with the constants of Lemma 4), Corollary 8 (monotonicity), Corollary 9 (large-population consequences), with the model and the standing assumption in Section 2. Published version: Journal of Mathematical Biology 76 (2018) 1–35, <https://doi.org/10.1007/s00285-017-1137-2>.
