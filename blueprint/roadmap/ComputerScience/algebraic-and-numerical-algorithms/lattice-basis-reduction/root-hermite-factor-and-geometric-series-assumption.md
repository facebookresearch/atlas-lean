# Root-Hermite factor and the geometric series assumption

The root-Hermite factor $\delta_0$ of a basis is defined by $\|b_1\|=\delta_0^{d}\operatorname{vol}(\Lambda)^{1/d}$. The geometric series assumption models the Gram–Schmidt norms of a reduced basis as a geometric sequence; if it holds, the ratio must be $\delta_0^{-2d/(d-1)}$.

Let $B=(b_1,\dots,b_d)$ be a basis of a lattice $\Lambda$ of rank $d$, with Gram–Schmidt vectors $b_i^*$.

**Hermite and root-Hermite factor.** The Hermite factor of $B$ is $\|b_1\|/\operatorname{vol}(\Lambda)^{1/d}$, and the root-Hermite factor is the unique $\delta_0>0$ with

$$
\|b_1\| = \delta_0^{\,d}\,\operatorname{vol}(\Lambda)^{1/d}.
$$

**Geometric series assumption (GSA).** A basis satisfies the GSA if there is $0<\alpha<1$ with $\|b_i^*\| = \alpha^{\,i-1}\|b_1\|$ for $1\le i\le d$. If $d\ge2$ and the GSA holds, then, because $\prod_{i=1}^{d}\|b_i^*\|=\operatorname{vol}(\Lambda)$,

$$
\alpha=\delta_0^{-2d/(d-1)} .
$$

The GSA is an assumption about bases produced by lattice reduction, not a consequence of being reduced.

**BKZ model.** Concrete analyses assume that a BKZ-$\beta$-reduced basis satisfies the GSA and has

$$
\delta_0\approx\Bigl(\frac{\beta}{2\pi e}\,(\pi\beta)^{1/\beta}\Bigr)^{1/(2(\beta-1))},
$$

a formula Albrecht, Göpfert, Virdia and Wunderer take from Chen's thesis. Both are modelling assumptions.

## Expansion

Given the GSA, $\prod_{i=1}^d\|b_i^*\|=\|b_1\|^d\alpha^{d(d-1)/2}$ and $\|b_1\|^d=\delta_0^{d^2}\operatorname{vol}(\Lambda)$, so $\delta_0^{d^2}\alpha^{d(d-1)/2}=1$, i.e. $\alpha=\delta_0^{-2d/(d-1)}$. The $\delta_0(\beta)$ formula is recorded as the model the cited papers use, attributed there to Chen's thesis; no claim about its accuracy is made, and it is not meant for very small block sizes.

## Depends on

- [The block Korkine–Zolotarev (BKZ) reduction algorithm](bkz-algorithm.md)

## Proof depends on

None.

## Sources

- Martin R. Albrecht, Florian Göpfert, Fernando Virdia, Thomas Wunderer, "Revisiting the Expected Cost of Solving uSVP and Applications to LWE", ASIACRYPT 2017, Lecture Notes in Computer Science 10624; IACR ePrint 2017/815, [https://eprint.iacr.org/2017/815](https://eprint.iacr.org/2017/815), Section 2.3 and Definition 3.
- Yuanmi Chen, Phong Q. Nguyen, "BKZ 2.0: Better Lattice Security Estimates", ASIACRYPT 2011, Lecture Notes in Computer Science 7073, pp. 1–20, [https://www.iacr.org/archive/asiacrypt2011/70730001/70730001.pdf](https://www.iacr.org/archive/asiacrypt2011/70730001/70730001.pdf), Section 2 (Hermite factor and the typical shape of reduced Gram–Schmidt norms).
- Martin Albrecht, Melissa Chase, Hao Chen, Jintai Ding, Shafi Goldwasser, Sergey Gorbunov, Shai Halevi, Jeffrey Hoffstein, Kim Laine, Kristin Lauter, Satya Lokam, Daniele Micciancio, Dustin Moody, Travis Morrison, Amit Sahai, Vinod Vaikuntanathan, "Homomorphic Encryption Standard", in Protecting Privacy through Homomorphic Encryption, Springer, 2021, pp. 31–62; IACR ePrint 2019/939, [https://eprint.iacr.org/2019/939](https://eprint.iacr.org/2019/939), Section 2.1.2.
