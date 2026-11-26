# Exact density of random minimizers for small windows

**Setting.** Fix an alphabet of size $\sigma\ge2$ and integers $k,w\ge2$. A *minimizer* with order $\rho$ on $k$-mers selects, in every window of $w$ consecutive $k$-mers (a string of length $w+k-1$), the position of its $\rho$-minimal $k$-mer. Its *density* is the expected fraction of selected positions in a random infinite $\sigma$-ary string. The *random minimizer* density $\mathcal{R}_\sigma(k,w)$ is the density averaged over a uniformly random order $\rho$; the density factor is $\mathcal{F}_\sigma(k,w)=(w+1)\mathcal{R}_\sigma(k,w)$. Let $\mathrm{Prim}_\sigma(p)$ be the number of primitive $\sigma$-ary words of length $p$ (not a proper power).

**General formula.** If a $(w+k)$-string $v$ contains $t$ distinct $k$-mers, the probability that a random order makes the last window of $v$ select a new position is $P_{\sigma,k}(v)=2/t$ if the $k$-suffix of $v$ occurs only once in $v$, and $1/t$ otherwise. Hence $\mathcal{R}_\sigma(k,w)=\sigma^{-(w+k)}\sum_{v\in\Sigma^{w+k}}P_{\sigma,k}(v)$, computable in $O(k\sigma^{w+k})$ time and $O(w+k)$ space.

**Theorem ($w\le k$).** If $w\le k$,

$$\mathcal{R}_\sigma(k,w)=\frac{2}{w+1}+\frac{\mathrm{dev}_\sigma(w)}{\sigma^{w+k}},$$

$$\mathrm{dev}_\sigma(w)=\sum_{t=1}^{w}\frac1t\Bigl(\mathrm{Prim}_\sigma(t)+\sum_{p=1}^{t-1}\mathrm{Prim}_\sigma(p)\,\sigma^{t-p}\Bigl(2t-2p+1-\frac{4t-4p-1}{\sigma}+\frac{2t-2p-2}{\sigma^2}\Bigr)\Bigr)-\frac{2}{w+1}\sum_{p=1}^{w}\mathrm{Prim}_\sigma(p)\,\sigma^{w-p}\Bigl(w-p+1-\frac{w-p}{\sigma}\Bigr),$$

which does not depend on $k$. So $\mathcal{R}_\sigma(k,w)$ is computable in $O(w^2)$ time independently of $\sigma$ and $k$ (the paper also gives an $O(w\log w)$ evaluation), and

$$\mathcal{R}_\sigma(k+1,w)=\frac{2}{w+1}+\frac1\sigma\Bigl(\mathcal{R}_\sigma(k,w)-\frac{2}{w+1}\Bigr),$$

so for fixed $w$ the density tends to $2/(w+1)$ at exact exponential rate $\sigma$ as $k\to\infty$.

**Theorem (sign of the deviation).** For every $\sigma\ge2$ there are $w_\sigma,w'_\sigma\ge11$ such that $\mathcal{F}_\sigma(k,w)>2$ for $2\le w\le\min\{w_\sigma,k\}$, while $\mathcal{F}_\sigma(k,w)<2$ for $w'_\sigma\le w\le k$, with $2-\mathcal{F}_\sigma(k,w)=\Theta\bigl(1/(w\sigma^k)\bigr)$. Thus random minimizers beat the folklore $2/(w+1)$ by a tiny margin once $w$ is moderately large.

**Large windows.** With $N=\sigma^k$ and $w=\frac{\sigma}{\sigma-1}N(\ln N+g(N))$ for a positive function $g$, $\mathcal{R}_\sigma(k,w)=(1+O(e^{-g(N)}))\sigma^{-k}$; and $\mathcal{R}_\sigma(k,w+1)\le\mathcal{R}_\sigma(k,w)$ always.

## Expansion

A new position is selected when sliding from one window to the next exactly when the minimal $k$-mer of the union of two consecutive windows is either the first or the last $k$-mer of that union; for a random order and $t$ distinct $k$-mers this has probability $2/t$, or $1/t$ when the last $k$-mer is repeated. If all $w+1$ $k$-mers are distinct this gives the leading $2/(w+1)$. For $w\le k$, any repeated $k$-mer forces a single periodic "major run" containing all repetitions, so strings with repetitions are counted by period $p$ via primitive words, which yields the closed form and its independence of $k$. A bijection between repetitive strings for $k$ and $k+1$ preserving selection probabilities gives the recursion in $k$.

## Sources

- S. Golan, A. M. Shur, "Expected Density of Random Minimizers", arXiv:2410.16968 (2024), Section 2 (general case: selection probability lemma, density as an average, quadratic-exponential algorithm), Section 3 (case $w\le k$: major runs, deviation formula, main formula, recursion in $k$, bijection, sign of the deviation), Section 4 (case $w>k$), <https://doi.org/10.48550/arXiv.2410.16968>.
