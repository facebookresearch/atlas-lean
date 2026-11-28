# Hardness of density estimation for Gaussian mixtures

An $\exp(g(n))$-time density estimator for mixtures of $2k+1$ Gaussians in $\mathbb{R}^n$, with $k$ an integer at least $2\gamma\sqrt{g(n)/\pi}$, yields an $O(\exp(g(n)))$-time algorithm that solves homogeneous CLWE, for $\beta<1/32$ and $\gamma\ge1$.

Let $\mathcal{G}_{n,k}$ be the family of mixtures of $k$ Gaussians in $\mathbb{R}^n$. *Density estimation* for $\mathcal{G}_{n,k}$: given $\delta>0$ and sample access to an unknown $P\in\mathcal{G}_{n,k}$, output with probability $9/10$ a distribution $Q$, as an evaluation oracle for its density, with total variation distance $\Delta(Q,P)\le\delta$. Fix $\delta=10^{-3}$.

**Theorem.** Let $\beta=\beta(n)\in(0,1/32)$, $\gamma=\gamma(n)\ge1$ and $g(n)\ge4\pi$, and let $k$ be an integer with $k\ge2\gamma\sqrt{g(n)/\pi}$. If an algorithm running in time $\exp(g(n))$ solves density estimation for $\mathcal{G}_{n,2k+1}$, then an algorithm running in time $O(\exp(g(n)))$ solves $\mathrm{hCLWE}_{\beta,\gamma}$, i.e. distinguishes $H_{w,\beta,\gamma}$ for a uniformly random unit $w$ from $D_{\mathbb{R}^n}$ with non-negligible advantage. On this page the advantage of a distinguisher is the absolute difference of its probabilities of answering "YES" under the two input laws; for the existence of a distinguisher with non-negligible advantage this is equivalent to using the signed difference, by relabelling the answer.

**Consequence.** Combined with the quantum hardness of homogeneous CLWE, which requires $\beta\in(0,1)$, $\gamma\ge2\sqrt n$ and $\gamma/\beta$ polynomially bounded: taking $\gamma=2\sqrt n$, $g(n)=c\log n$ for a constant $c$ with $g(n)\ge4\pi$, $k=\lceil2\gamma\sqrt{g(n)/\pi}\rceil$ and $\beta<1/32$ with $\gamma/\beta$ polynomially bounded, an algorithm that solves density estimation for $\mathcal{G}_{n,K}$ for every $K$ in time polynomial in $n$ and $K$ would, applied with $K=2k+1=O(\sqrt{n\log n})$, give a polynomial-time quantum algorithm for $\mathrm{SIVP}_\alpha$ and $\mathrm{GapSVP}_\alpha$ with $\alpha$ polynomial in $n$.

## Proof sketch

Bruna et al.'s proof runs the estimator on the unknown $P$, obtaining an evaluation oracle $f$, and tests whether $P=D_{\mathbb{R}^n}$: it draws a constant number of points $x\sim D_{\mathbb{R}^n}$ (about $1/(6\sqrt\delta)$) and answers "Gaussian" iff $f(x)/D(x)\in[1-\sqrt\delta,1+\sqrt\delta]$ for all of them. Two facts are proved. First, the estimator succeeds on both input laws with constant probability: for $P=D_{\mathbb{R}^n}$ because $D_{\mathbb{R}^n}\in\mathcal{G}_{n,2k+1}$; for $P=H_{w,\beta,\gamma}$, which has infinitely many components, because truncating to the $2k+1$ central components changes it by at most $2\exp(-\pi k^2/(\beta^2+\gamma^2))$ in total variation (Claim 5.4, any positive integer $k$), so the joint law of the $\exp(g(n))$ samples the estimator reads differs from the truncated one by at most $2\exp(-g(n))\le2e^{-4\pi}$, and on success $\Delta(f,H_{w,\beta,\gamma})<2\delta$ by the triangle inequality. Second, $\Delta(H_{w,\beta,\gamma},D_{\mathbb{R}^n})>1/2$ for $\beta<1/32$, $\gamma\ge1$ (Claim 5.3). The remaining step, that the ratio test turns these facts into a distinguisher, is asserted by the source without a quantitative argument: it states success probability at least $2/3$ and calls Rubinfeld and Servedio's Observation 24 a closely related statement. The source writes $k=2\gamma\sqrt{g(n)/\pi}$; any integer at least this value works in the truncation argument. Gupte, Vafa and Vaikuntanathan derive related bounds from classical LWE hardness under their own time, sample and advantage assumptions.

## Expansion

A good expansion adds pages for:

- the total variation gap $\Delta(H_{w,\beta,\gamma},D_{\mathbb{R}^n})>1/2$ for $\beta<1/32$, $\gamma\ge1$ (Bruna–Regev–Song–Tang, Claim 5.3);
- the truncation bound for $H_{w,\beta,\gamma}$ to its $2k+1$ central components (Bruna–Regev–Song–Tang, Claim 5.4);
- a quantitative analysis of the ratio test that turns an accurate density estimate into a distinguisher with non-negligible advantage.

## Depends on

- [Homogeneous continuous learning with errors (hCLWE)](homogeneous-continuous-lwe.md)
- [Total variation distance between finite measures](../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)
- [Distinguishing advantage](../../cryptography/security-games/games-and-advantages/advantage.md)

## Proof depends on

- [Quantum worst-case hardness of continuous LWE](hardness-of-continuous-lwe-from-lattice-problems.md)

## Sources

- Joan Bruna, Oded Regev, Min Jae Song, Yi Tang, "Continuous LWE", ACM STOC 2021; numbers from arXiv:2005.09595v2: Definition 5.1, Proposition 5.2 and Claims 5.3–5.4, and Corollary 4.2.
- Aparna Gupte, Neekon Vafa, Vinod Vaikuntanathan, "Continuous LWE is as Hard as LWE & Applications to Learning Gaussian Mixtures", IEEE FOCS 2022; numbers from arXiv:2204.02550v3, Section 6.
