# Coalescence times of a critical Galton–Watson process with immigration

**Model.** Let $(p_j)_{j\ge0}$ (offspring law) and $(b_j)_{j\ge0}$ (immigration law) be probability distributions on $\{0,1,2,\dots\}$. The Galton–Watson process with immigration (GWPI) is

$$Z_0=I_0,\qquad Z_{n+1}=\sum_{i=1}^{Z_n}\xi_{n,i}+I_{n+1},$$

with all $\xi_{n,i}\sim(p_j)$ and $I_n\sim(b_j)$ independent. Immigrants are assumed to have pairwise distinct ancestors. Assume

$$0<p_0+p_1<1,\qquad m=\sum_j jp_j=1,\qquad \sigma^2=\sum_j j^2p_j-1<\infty,\qquad b_0<1,\qquad \beta=\sum_j jb_j<\infty,$$

and put $\gamma=2\beta/\sigma^2$.

Conditional on $\{Z_n>1\}$, pick two distinct individuals of generation $n$ uniformly. Their **pairwise coalescence time** $X^I_n$ is the generation of their most recent common ancestor, with $X^I_n=\infty$ if they descend from different immigrants. Conditional on $\{Z_n>0\}$, the **total coalescence time** $A^I_n$ is the generation of the most recent common ancestor of all individuals alive at time $n$ ($\infty$ if none exists).

**Theorem.** Let $(\omega_i)_{i\ge1}$ be i.i.d. exponential with rate $2/\sigma^2$, let $W$ be a Poisson random measure on $(0,\infty)$ with intensity $\frac{\gamma}{r}e^{-2r/\sigma^2}\,dr$, and for $0<u<1$ let $N^I_u$ be negative binomial,

$$\mathbb P(N^I_u=k)=\binom{\gamma+k-1}{k}(1-u)^{\gamma}u^{k},\qquad k=0,1,2,\dots,$$

with $(\omega_i)$, $W$, $N^I_u$ independent. Write $\langle f,\mu\rangle=\int r\,\mu(dr)$, $\langle f^2,\mu\rangle=\int r^2\mu(dr)$ and

$$\phi(j,\mu)=\mathbb E\left[\frac{\sum_{i=1}^{j}\omega_i^2+\langle f^2,\mu\rangle}{\big(\sum_{i=1}^{j}\omega_i+\langle f,\mu\rangle\big)^2}\right].$$

Then:
1. for $0<u<1$, $\displaystyle\lim_{n\to\infty,\ k/n\to u}\mathbb P\big(k\le X^I_n<n\,\big|\,Z_n>1\big)=\mathbb E\,\phi(N^I_u,W)$;
2. $\displaystyle\lim_{n\to\infty}\mathbb P\big(X^I_n<\infty\,\big|\,Z_n>1\big)=\mathbb E\left[\frac{\langle f^2,W\rangle}{\langle f,W\rangle^2}\right]$;
3. $\displaystyle\lim_{n\to\infty}\mathbb P\big(A^I_n<\infty\,\big|\,Z_n>0\big)=0$;
4. if $\tau_n$ is the immigration generation of the oldest immigrant family with descendants alive at time $n$, then $\lim_{n\to\infty,\,k/n\to u}\mathbb P(\tau_n>k)=(1-u)^{\gamma}$.

Without immigration (one ancestor, conditioned on $Y_n\ge2$) the analogous limit of Athreya has a geometric number $N_u\ge1$ of exponential families; with immigration $N^I_u$ can be $0$, and when $\gamma=1$ the law of $N^I_u+1$ is that geometric law.

## Expansion

Two individuals sampled at time $n$ have coalesced at or after generation $k$ exactly when both descend from the same individual of generation $k$ or from the same later immigrant. Hence

$$\mathbb P(k\le X^I_n<n\mid Z_n>1)=\mathbb E\left[\frac{\sum_i (Y_{n,k,i})_2+\sum_{j>k}\sum_{l\le I_j}(Y^{(j)}_{n-j,l})_2}{(Z_n)_2}\,\Big|\,Z_n>1\right],$$

where $(y)_2=y(y-1)$ and the $Y$'s are family sizes at time $n$. By Yaglom's theorem a surviving critical family of age $n-k$ has size $\approx(n-k)\omega$ with $\omega$ exponential of mean $\sigma^2/2$; the number of the $Z_k\approx n\cdot\mathrm{Gamma}$ families of generation $k$ that survive is asymptotically negative binomial $N^I_u$, and the surviving immigrant families founded after $k$ form, after rescaling, the Poisson measure $W$. Plugging these point-process limits into the ratio gives (1)–(2). For (3), infinitely many immigrant families survive in the limit ($W$ has infinite mass near $0$), so a single common ancestor of the whole population has vanishing probability. Statement (4) is the event that no generation-$k$ family survives, $\mathbb P(N^I_u=0)=(1-u)^\gamma$.

## Sources

- Rong-Li Liu, Yan-Xia Ren and Yingrui Wang, "Coalescence times for critical Galton–Watson processes with immigration", *Statistics & Probability Letters* 210 (2024), 110121, <https://doi.org/10.1016/j.spl.2024.110121>. Numbering as in the preprint arXiv:2307.07384v1, <https://arxiv.org/abs/2307.07384v1>: Section 1, Assumption 1, Theorems 1.1 and 1.2; Section 2, Lemmas 2.2–2.4 and Corollary 2.6.
