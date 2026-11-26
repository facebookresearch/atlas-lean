# Central limit theorem for block counts of the Ewens–Pitman partition with $\theta$ proportional to $n$

**Setting.** The Ewens–Pitman model with parameters $\alpha\in[0,1)$ and $\theta>-\alpha$ is the law of the random partition of $\{1,\dots,n\}$ built sequentially (the Chinese restaurant process). Given $j$ blocks of sizes $n_1,\dots,n_j$ after $h$ elements, element $h+1$ starts a new block with probability $\frac{\theta+j\alpha}{\theta+h}$ and joins block $i$ with probability $\frac{n_i-\alpha}{\theta+h}$. The case $\alpha=0$ is the Ewens sampling formula of the infinitely-many-alleles model with $\theta=4N\mu$. Consider the regime $\theta=\lambda n$ with $\lambda>0$ fixed, a high-mutation regime. Let $K_n$ be the number of blocks and $K_{r,n}$ the number of blocks of size $r$, and set $\mathbf K_{d,n}=(K_n,K_{1,n},\dots,K_{d,n})$.

**Theorem.** Fix $d\ge1$. Define

$$\mathfrak m_0=\begin{cases}\dfrac{\lambda}{\alpha}\Big[\Big(\dfrac{\lambda+1}{\lambda}\Big)^{\alpha}-1\Big],&\alpha\in(0,1),\\[2mm] \lambda\log\dfrac{\lambda+1}{\lambda},&\alpha=0,\end{cases}\qquad \mathfrak m_r=\frac{(1-\alpha)_{\uparrow r-1}}{r!}\,\lambda^{1-\alpha}(1+\lambda)^{\alpha-r}\quad(r\ge1),$$

where $(a)_{\uparrow k}=a(a+1)\cdots(a+k-1)$, and let $\mathfrak M_d=(\mathfrak m_0,\mathfrak m_1,\dots,\mathfrak m_d)$. As $n\to\infty$:

1. $\mathbb E[\mathbf K_{d,n}]=n\,\mathfrak M_d+O(1)$;
2. (SLLN) $\mathbf K_{d,n}/n\to\mathfrak M_d$ almost surely;
3. (CLT) $\dfrac{\mathbf K_{d,n}-n\,\mathfrak M_d}{\sqrt n}\Rightarrow\mathcal N(\mathbf 0,\Sigma_{d,\alpha,\lambda})$,

for an explicit positive semidefinite $(d+1)\times(d+1)$ covariance matrix $\Sigma_{d,\alpha,\lambda}$ depending only on $\alpha$ and $\lambda$.

## Expansion

Both $K_n$ and the $K_{r,n}$ grow linearly in $n$ here, unlike the classical fixed-$\theta$ regime, where $K_n\sim\theta\log n$ ($\alpha=0$) or $K_n\sim S_\alpha n^\alpha$ with a random limit. The proof embeds the sequential construction into a triangular array of martingales. After $h=\lfloor xn\rfloor$ arrivals, the conditional mean increments of $K_{r,h}$ are explicit affine functions of the current block counts. The compensated vector $\mathbf M_{d,h}$ is a martingale in $h$. A uniform SLLN along the path, $K_{r,\lfloor xn\rfloor}/n\to m_r(x)=\frac{(1-\alpha)_{\uparrow r-1}}{r!}x^r\lambda^{1-\alpha}(x+\lambda)^{\alpha-r}$, identifies the limit of the normalized predictable quadratic variation. A Lindeberg-type martingale CLT for triangular arrays then gives the Gaussian limit, and integrating the variance along $x\in[0,1]$ gives $\Sigma$. In population-genetic terms this gives Gaussian confidence statements for the number of distinct alleles and of singleton, doubleton, … alleles in a large sample when mutation is strong.

## Sources

- B. Bercu, C. Contardi, E. Dolera, S. Favaro, "A Central Limit Theorem for the Ewens–Pitman random partition in the large-$\theta$ regime via a martingale approach", arXiv:2601.18935 (2026): Theorem 1.1 (moments, SLLN and joint CLT), Corollaries 1.2–1.3 (number of blocks and blocks of size $r$), Lemma 2.1 (uniform SLLN along the path), Lemmas 2.2–2.3 (martingale structure and CLT criterion). <https://doi.org/10.48550/arXiv.2601.18935>
