# Hardness of LWE with sparse ternary secrets

If standard decision LWE in dimension $\ell$ is hard, then decision LWE whose secret is uniform among ternary vectors with exactly $k$ nonzero entries is hard, provided $k\log_2(n/k)$, a lower bound on the secret's min-entropy, exceeds $(\ell+1)\log_2 q$ by $\omega(\log\lambda)$; the error grows to $2\sigma\sqrt{k+1}$.

Let $S_{n,k}$ be the uniform distribution on vectors in $\{-1,0,1\}^n$ with exactly $k$ nonzero entries, $1<k<n$. Write $\mathrm{LWE}(N,\mathbb{Z}_q^{d},\mathcal{S},D_{\mathbb{Z},\sigma})$ for $N$ LWE samples with vectors uniform in $\mathbb{Z}_q^{d}$, a secret drawn from $\mathcal{S}$ and error from the discrete Gaussian $D_{\mathbb{Z},\sigma}$ of width $\sigma$; the comparison distributions are uniform on the corresponding product sets, and $\lambda$ is the security parameter.

**Theorem.** Suppose $\log(q)/2^{\ell}=\mathrm{negl}(\lambda)$, $\sigma\ge 4\sqrt{\omega(\log\lambda)+\ln n+\ln m}$, and

$$
k\log_2(n/k)\ \ge\ (\ell+1)\log_2 q+\omega(\log\lambda).
$$

If $\mathrm{LWE}(n,\mathbb{Z}_q^{\ell},\mathbb{Z}_q^{\ell},D_{\mathbb{Z},\sigma})$ and the uniform distribution on $\mathbb{Z}_q^{\ell\times n}\times\mathbb{Z}_q^{n}$ have no distinguisher running in time $T+\mathrm{poly}(n,m,q,\lambda)$ with advantage $\epsilon$, then $\mathrm{LWE}(m,\mathbb{Z}_q^{n},S_{n,k},D_{\mathbb{Z},\sigma'})$ and the uniform distribution on $\mathbb{Z}_q^{n\times m}\times\mathbb{Z}_q^{m}$ have no $T$-time distinguisher with advantage $2\epsilon m+\mathrm{negl}(\lambda)$, where $\sigma'=2\sigma\sqrt{k+1}$.

The entropy in the hypothesis is that of the integer distribution $S_{n,k}$ on $\{-1,0,1\}^n$: its min-entropy is $\log_2\bigl(\binom nk2^k\bigr)\ge k\log_2(n/k)$, and the hypothesis uses the lower bound. The secret residue $S_{n,k}\bmod q$ can have smaller entropy when $q=2$, where the signs collapse. For fixed small $k$ the inequality caps the admissible $\ell$: for $n=512$ and $k=20$, $k\log_2(n/k)\approx94$, so with $\log_2q=10$ it allows only $\ell\le8$. This bounds what this reduction gives; it is not a statement about such instances.

## Expansion

Gupte, Vafa and Vaikuntanathan adapt Micciancio's binary-secret reduction. A transformation $\varphi$ built from a gadget matrix adapted to $k$-sparse vectors (their Lemma 11, Section 4) maps the uniform distribution to a distribution statistically close to sparse-secret LWE with error $\sigma'$, using the min-entropy bound (their Lemma 10, from $|S_{n,k}|=\binom nk2^k$ and $\binom nk\ge(n/k)^k$); and it maps the first matrix-secret LWE distribution (dimension $n-1$, secret size $\ell$) to a distribution statistically close to the second (dimension $n+1$, secret size $\ell+1$, error $2\sigma$). Hence sparse-secret LWE $\approx\varphi(\text{uniform})\approx_c\varphi(\text{first})\approx\text{second}\approx_c$ uniform. Their Theorem 5 assumes hardness of two matrix-secret LWE distributions, in dimensions $n-1$ and $n+1$ with secret sizes $\ell$ and $\ell+1$; the corollary above derives both from the single assumption, with the hybrid over $m$ secret columns giving the factor $m$. The proof uses the sparse gadget lemma, the discrete Gaussian convolution lemma and the matrix-secret hybrid lemma.

## Depends on

- [LWE with a prescribed secret distribution](lwe-with-a-secret-distribution.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)
- [Gaussian function, Gaussian mass and discrete Gaussian on a lattice](../lattice-gaussians-and-smoothing-parameter/discrete-gaussian-on-a-lattice.md)
- [Distinguishing advantage](../../../security-games/games-and-advantages/advantage.md)

## Proof depends on

None.

## Sources

- Aparna Gupte, Neekon Vafa, Vinod Vaikuntanathan, "Continuous LWE is as Hard as LWE & Applications to Learning Gaussian Mixtures", IEEE FOCS 2022; numbers from arXiv:2204.02550v3, Section 4: Definition 10, Lemma 10, Lemma 11, Theorem 5 and Corollary 4.
