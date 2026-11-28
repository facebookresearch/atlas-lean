# LWE with a prescribed secret distribution

Restricted-secret LWE keeps the uniform matrix and the error of LWE but draws the secret from a prescribed distribution on $\mathbb{Z}_q^n$, typically the reduction modulo $q$ of an integer vector with small entries: binary, sign, ternary, centered binomial, rounded Gaussian, or one of these with a fixed number of nonzero entries.

Fix integers $n,m\ge1$ and $q\ge2$, an error distribution $\chi_e$ on $\mathbb{Z}_q$, and a secret distribution $\chi_s$ on $\mathbb{Z}_q^n$. The distribution $\mathrm{LWE}(n,m,q,\chi_s,\chi_e)$ outputs $(A,\,As+e)$ with $A$ uniform in $\mathbb{Z}_q^{m\times n}$, $s\sim\chi_s$ and $e\sim\chi_e^{m}$ independent. The *search* problem asks for $s\in\mathbb{Z}_q^n$; the *decision* problem asks to distinguish this distribution from the uniform distribution on $\mathbb{Z}_q^{m\times n}\times\mathbb{Z}_q^{m}$.

In practice $\chi_s$ is the law of $\bar s \bmod q$ for an integer vector $\bar s\sim\chi$ drawn from a distribution $\chi$ on $\mathbb{Z}^n$:

- *binary*: $\chi$ uniform on $\{0,1\}^n$ (Micciancio's $\mathrm{LWE}_{0,1}$);
- *sign*: $\chi$ uniform on $\{-1,1\}^n$ ($\mathrm{LWE}_{\pm}$);
- *ternary*: independent coordinates uniform on $\{-1,0,1\}$;
- *centered binomial* $B_\eta$: each coordinate $\sum_{i=1}^{\eta}(a_i-b_i)$ for independent uniform bits;
- *rounded Gaussian* $N(\sigma)$: each coordinate a centred normal of standard deviation $\sigma$ rounded to the nearest integer;
- *fixed weight $h$*: one of the above conditioned on the event that the integer vector $\bar s$ has exactly $h$ nonzero coordinates, defined when that event has positive probability (for binary and ternary, $0\le h\le n$; for sign vectors only $h=n$). The weight is that of $\bar s$ at the sampling stage; after reduction modulo a small $q$ it can differ (for $q=2$ the sign vector $\bar s$ reduces to the all-ones residue vector). For binary secrets $h$ is the Hamming weight and $h/n$ the sparsity. Gupte, Vafa and Vaikuntanathan write $S_{n,h}$ for the uniform distribution on vectors of $\{-1,0,1\}^n$ with exactly $h$ nonzero entries.

**Recovering the integer vector.** If the support of $\chi$ lies in a set of integer vectors on which reduction modulo $q$ is injective, for instance $(-q/2,q/2]^n$, then $s$ determines $\bar s$, so search for $s$ also recovers $\bar s$. This holds for binary secrets when $q\ge2$, for sign and ternary secrets when $q\ge3$, and for $B_\eta$ when $q>2\eta$; it fails for the rounded Gaussian, whose support is all of $\mathbb{Z}$.

Binary, ternary and sparse secrets are used for efficiency in homomorphic encryption and centered binomial secrets in Kyber. The Homomorphic Encryption Standard tabulates parameters for uniform, error-distributed and ternary secrets and none for sparse secrets, whose security implications it describes as not yet well understood.

## Remarks

This page fixes notation; hardness results are separate pages. Their hypotheses differ from family to family: Micciancio's theorem for sign secrets needs $n+1\ge(k+1)(\log_2q+1)$ for an underlying standard LWE dimension $k$, and the sparse-secret theorem of Gupte, Vafa and Vaikuntanathan needs $h\log_2(n/h)$ to exceed $(\ell+1)\log_2q$ by $\omega(\log\lambda)$; Micciancio's theorem concerns full-weight sign secrets, and for $h=64$, $n=2^{14}$ the sparse-secret theorem's left side is $64\log_2256=512$, so it derives hardness only from standard LWE of dimension $\ell<512/\log_2q-1$. These are limits of the cited reductions, not hardness or easiness statements for such instances.

## Depends on

- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)
- [The centered binomial distribution](../module-lattice-encryption/centered-binomial-distribution.md)

## Proof depends on

None.

## Sources

- Emily Wenger, Eshika Saxena, Mohamed Malhou, Ellie Thieu, Kristin Lauter, "Benchmarking Attacks on Learning with Errors", IEEE Symposium on Security and Privacy 2025, https://doi.org/10.1109/SP61157.2025.00058; numbers from arXiv:2408.00882v2, Section 2.1.
- Daniele Micciancio, "On the Hardness of Learning With Errors with Binary Secrets", Theory of Computing 14(13):1–17, 2018, https://doi.org/10.4086/toc.2018.v014a013, Definitions 2.10 and 2.11.
- Aparna Gupte, Neekon Vafa, Vinod Vaikuntanathan, "Continuous LWE is as Hard as LWE & Applications to Learning Gaussian Mixtures", IEEE FOCS 2022; numbers from arXiv:2204.02550v3, Section 4, Definition 10.
- Martin Albrecht, Melissa Chase, Hao Chen, Jintai Ding, Shafi Goldwasser, Sergey Gorbunov, Shai Halevi, Jeffrey Hoffstein, Kim Laine, Kristin Lauter, Satya Lokam, Daniele Micciancio, Dustin Moody, Travis Morrison, Amit Sahai, Vinod Vaikuntanathan, "Homomorphic Encryption Standard", version of November 21, 2018, HomomorphicEncryption.org, [https://homomorphicencryption.org/wp-content/uploads/2018/11/HomomorphicEncryptionStandardv1.1.pdf](https://homomorphicencryption.org/wp-content/uploads/2018/11/HomomorphicEncryptionStandardv1.1.pdf), Section 2.1.5, Secret key (PDF p. 24).
