# Continuous LWE is as hard as LWE

Gupte–Vafa–Vaikuntanathan reduce standard decision LWE in dimension $\ell$ to decision CLWE in dimension $n\ge2\ell\log_2q+\omega(\log\lambda)$, with frequency $\gamma=\sqrt n\sqrt{\ln m+\ln n+\omega(\log\lambda)}$ and noise $\beta=O(\sigma\sqrt n/q)$ produced by the reduction, losing a factor $2m$ in advantage.

Write $\mathrm{CLWE}(m,D_1^n,\gamma,\beta)$ for $m$ CLWE samples in dimension $n$ with vectors from $D_{\mathbb{R}^n}$ and a uniformly random unit secret, $\mathbb{T}=[0,1)$, and $\mathrm{LWE}(m,\mathbb{Z}_q^{\ell},\mathbb{Z}_q^{\ell},D_{\mathbb{Z},\sigma})$ for $m$ standard LWE samples with uniform secret in $\mathbb{Z}_q^{\ell}$; $\lambda$ is the security parameter.

**Theorem.** Let $q,\ell,n,m\in\mathbb{N}$ with $m>n$ and $\sigma,\epsilon>0$, and assume $\log(q)/2^{\ell}=\mathrm{negl}(\lambda)$, $n\ge 2\ell\log_2q+\omega(\log\lambda)$ and $\sigma\ge C\sqrt{\ln m+\omega(\log\lambda)}$ for a universal constant $C$. The reduction produces the parameters

$$
\gamma=\sqrt n\cdot\sqrt{\ln m+\ln n+\omega(\log\lambda)},\qquad \beta=\frac{\sigma_3}{q}\ \text{ for a width }\sigma_3=O(\sigma\sqrt n),
$$

so that $\beta=O(\sigma\sqrt n/q)$. If no algorithm running in time $T+\mathrm{poly}(\ell,n,m,\log q,\log\sigma,\log\lambda)$ distinguishes $\mathrm{LWE}(m,\mathbb{Z}_q^{\ell},\mathbb{Z}_q^{\ell},D_{\mathbb{Z},\sigma})$ from uniform with advantage $(\epsilon-\mathrm{negl}(\lambda))/(2m)$, then no $T$-time algorithm distinguishes $\mathrm{CLWE}(m,D_1^n,\gamma,\beta)$ from $D_1^{n\times m}\times U(\mathbb{T}^m)$ with advantage $\epsilon$.

Meaningful parameters ($\beta\ll1$) need $q/\sigma\gg\sqrt n$.

## Proof sketch

The proof (Corollary 5) has three steps. First, a quantitative form of Micciancio's binary-secret reduction (Gupte–Vafa–Vaikuntanathan, Theorem 7, from Micciancio's Theorem 3.1 and Lemma 2.9) gives hardness of LWE with secrets uniform on $\{-1,1\}^n$, $m$ samples and error width $\sigma_1=2\sigma\sqrt{n+1}$, at advantage $\epsilon$ from advantage $(\epsilon-\mathrm{negl})/(2m)$ for standard LWE with $n$ samples. Second, the dimension- and sample-preserving reduction from LWE with secrets of fixed norm $r$ to CLWE with secret distribution $\frac1r\mathcal{S}$ (their Theorem 6) applies with $r=\sqrt n$, yielding the stated $\gamma$ and $\beta=\sigma_3/q$, provided $\sigma_1\ge3\sqrt n\sqrt{\ln m+\ln n+\omega(\log\lambda)}$, which the hypothesis on $\sigma$ guarantees. Third, a uniformly random rotation applied to all samples turns the discrete secret $\frac1{\sqrt n}\{-1,1\}^n$ into a uniform unit vector (Claim 2.22 of Bruna et al.). A separate corollary (their Corollary 3) combines the result with classical hardness of LWE for worst-case GapSVP, and Corollary 6 treats sparse secrets; both have their own parameter regimes and are not part of this statement.

## Expansion

A good expansion adds pages for:

- the quantitative sign-secret step with its finite advantage loss (Gupte–Vafa–Vaikuntanathan, Theorem 7); the asymptotic binary-secret hardness page does not provide this interface;
- the dimension- and sample-preserving reduction from LWE with secrets of fixed norm to CLWE (Gupte–Vafa–Vaikuntanathan, Theorem 6).

## Depends on

- [Continuous learning with errors (CLWE)](continuous-lwe.md)
- [Learning with errors](../../cryptography/public-key/hardness-assumptions/learning-with-errors.md)
- [Distinguishing advantage](../../cryptography/security-games/games-and-advantages/advantage.md)
- [Gaussian function, Gaussian mass and discrete Gaussian on a lattice](../../cryptography/public-key/lattice-and-code-based-cryptography/lattice-gaussians-and-smoothing-parameter/discrete-gaussian-on-a-lattice.md)

## Proof depends on

- [LWE with a prescribed secret distribution](../../cryptography/public-key/lattice-and-code-based-cryptography/small-and-sparse-secret-lwe/lwe-with-a-secret-distribution.md)

## Sources

- Aparna Gupte, Neekon Vafa, Vinod Vaikuntanathan, "Continuous LWE is as Hard as LWE & Applications to Learning Gaussian Mixtures", IEEE FOCS 2022; numbers from arXiv:2204.02550v3: Theorem 6, Theorem 7, Corollary 5 with its proof, and Remark 3.
- Joan Bruna, Oded Regev, Min Jae Song, Yi Tang, "Continuous LWE", ACM STOC 2021; numbers from arXiv:2005.09595v2, Claim 2.22.
