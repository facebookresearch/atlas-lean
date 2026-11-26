# Adiabatic reduction of the bursty mRNA–protein PDMP

Let $x_1,x_2\ge0$ be mRNA and protein concentrations in the piecewise-deterministic Markov model

$$\frac{dx_1}{dt}=-g_1x_1+\mathring{N}\big(h,\lambda_1(x_2)\big),\qquad \frac{dx_2}{dt}=-g_2x_2+k_2x_1,$$

where $\mathring{N}(h,\lambda_1(x_2))$ is compound Poisson transcription: bursts arrive at rate $\lambda_1(x_2)$ and have size density $h$ on $[0,\infty)$. Assume $\lambda_1\in C^1$ is globally Lipschitz with $0\le\lambda_1(x)\le c+Kx$, $h$ is continuous, and the mean burst size $b=\int_0^\infty xh(x)\,dx$ is finite. Let mRNA degradation be fast, $g_1^n=ng_1$, under one of three scalings:

- (S1) frequent transcription: $\lambda_1^n=n\lambda_1$, with $k_2,h$ fixed;
- (S2) large mRNA bursts: $h^n(z)=\frac1nh(z/n)$, with $\lambda_1,k_2$ fixed;
- (S3) fast translation: $k_2^n=nk_2$, with $\lambda_1,h$ fixed.

**Statement.** Suppose $x_2^n(0)\to x_2^0$.

1. Under (S1), $x_1^n$ does not converge in any functional sense, while $x_2^n$ converges in law in the Skorokhod space $D[0,\infty)$ to the solution of the ODE $\dot x_2=-g_2x_2+\frac{bk_2}{g_1}\lambda_1(x_2)$, $x_2(0)=x_2^0$.
2. Under (S2), $x_1^n/n\to0$ and $x_2^n$ converges in law, in $L^p$ ($1\le p<\infty$) and in $D[0,T]$ with the Jakubowski topology, to the one-dimensional bursting PDMP $\dot x_2=-g_2x_2+\mathring{N}(\bar h,\lambda_1(x_2))$ with rescaled burst density $\bar h(y)=\frac{g_1}{k_2}h\big(\frac{g_1}{k_2}y\big)$.
3. Under (S3), $x_1^n\to0$ in the same sense, and $x_2^n$ converges to a bursting PDMP of the same form, with burst density $\bar h$.

Thus mRNA bursts are transmitted to protein bursts (scaled by the mean number of proteins per mRNA, $k_2/g_1$) when bursts are large or translation is fast, but are averaged into a deterministic production rate when transcription is merely frequent.

## Expansion

Quasi-stationarity of the fast mRNA gives $x_1^n\approx\frac{1}{g_1^n}\mathring{N}(h^n,\lambda_1^n(x_2^n))$, so the protein sees jumps of size $\frac{k_2^n}{g_1^n}\times$(mRNA burst) at rate $\lambda_1^n$. Under (S1) the jumps have size $O(1/n)$ and rate $O(n)$, a law-of-large-numbers regime; under (S2) and (S3) jump sizes and rates stay $O(1)$. The proof derives moment bounds from the generator, proves tightness (in the Jakubowski topology for the scalings where $x_1^n$ has spikes), and identifies the limit through the martingale problem. In (S2) the mRNA spikes are very large, in (S3) mRNA is rarely present but efficiently translated, yet the protein limits agree.

## Sources

- R. Yvinec, *Adiabatic reduction of models of stochastic gene expression with bursting*, arXiv:1301.1293 (2013), <https://doi.org/10.48550/arXiv.1301.1293>. Hypothesis 2 and Theorems 3, 4 and 5 (Section 2, statement of the results).
