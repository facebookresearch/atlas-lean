# Hardness of LWE with sign secrets from standard LWE

Micciancio's theorem: if standard LWE with secret dimension $k$ and $n+1$ samples is pseudorandom, then LWE with a uniform $\pm1$ secret in dimension $n\ge(k+1)(\log_2q+1)-1$ is pseudorandom for any polynomial number of samples, with error parameter $2\sigma\sqrt{n+1}$. For odd $q$ the same holds for binary secrets.

Write $\mathrm{LWE}(q,k,N,\sigma)$ for LWE with modulus $q$, uniform secret in $\mathbb{Z}_q^{k}$, $N$ samples and error from the discrete Gaussian $D_\sigma$ on $\mathbb{Z}$, and $\mathrm{LWE}_{\pm}(q,n,m,\hat\sigma)$ for the same with secret uniform on $\{-1,1\}^n$ and $m$ samples. All quantities are functions of the index $n$; an ensemble is *pseudorandom* if every probabilistic polynomial-time algorithm distinguishes it from uniform with advantage negligible in $n$.

**Theorem.** Assume $\mathrm{LWE}(q,k,n+1,\sigma)$ is pseudorandom for some $q\le 2^{n^{O(1)}}$, $\sigma\ge\omega(\sqrt{\log n})$, $k\ge\omega(\log n)$ with

$$
n+1\ \ge\ (k+1)\bigl(\log_2 q+1\bigr).
$$

Then $\mathrm{LWE}_{\pm}(q,n,m,\hat\sigma)$ is pseudorandom for every $m=n^{O(1)}$ and $\hat\sigma=2\sigma\sqrt{n+1}$.

**Corollary.** If moreover $q$ is odd, LWE with secret uniform on $\{0,1\}^n$, $m=n^{O(1)}$ samples and error $D_{\hat\sigma}$ is pseudorandom, by the equivalence of binary and sign secrets.

The assumption uses the fixed number $n+1$ of samples; the conclusion allows any polynomial number. Micciancio notes that the proof adapts to other adversary classes, for instance subexponential time.

## Expansion

Micciancio's Theorem 3.1 defines an efficient transformation $\varphi$ that maps a uniform matrix to a distribution statistically close to $\mathrm{LWE}_{\pm}(q,n,m,\hat\sigma)$ (his Claim 3.2), and maps samples of the matrix-secret distribution $\mathrm{LWE}(q,k\times m,n-1,\sigma)$ to a distribution statistically close to $\mathrm{LWE}(q,(k+1)\times m,n+1,2\sigma)$. If both matrix-secret distributions are pseudorandom, then $\mathrm{LWE}_{\pm}\approx\varphi(\text{uniform})\approx_c\varphi(\mathrm{LWE}(q,k\times m,n-1,\sigma))\approx\mathrm{LWE}(q,(k+1)\times m,n+1,2\sigma)\approx_c\text{uniform}$. Corollary 3.4 derives both hypotheses from the single assumption above: drop two samples; add an independent discrete Gaussian of parameter $\sqrt3\sigma$ and extend the secret by one coordinate; and pass from vector to matrix secrets by the hybrid argument (his Lemma 2.9). The proof uses his gadget matrix (Lemma 2.7) and the discrete Gaussian convolution lemma (Lemma 2.5). The smallest admissible $n$ is about $(k+1)(\log_2q+1)$; Brakerski, Langlois, Peikert, Regev and Stehlé prove a comparable binary-secret step inside the existing classical-hardness page.

## Depends on

- [LWE with a prescribed secret distribution](lwe-with-a-secret-distribution.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)
- [Gaussian function, Gaussian mass and discrete Gaussian on a lattice](../lattice-gaussians-and-smoothing-parameter/discrete-gaussian-on-a-lattice.md)
- [Distinguishing advantage](../../../security-games/games-and-advantages/advantage.md)

## Proof depends on

- [Binary and sign secrets give equivalent LWE problems for odd moduli](binary-and-sign-secret-lwe-equivalence.md)

## Sources

- Daniele Micciancio, "On the Hardness of Learning With Errors with Binary Secrets", Theory of Computing 14(13):1–17, 2018, https://doi.org/10.4086/toc.2018.v014a013, Section 2.4 (pseudorandomness), Theorem 3.1, Claim 3.2, Corollary 3.4 and Section 4.
