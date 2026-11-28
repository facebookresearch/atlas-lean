# Root-Hermite factor and the geometric series assumption

The root-Hermite factor $\delta_0$ of a basis is defined by $\|b_1\|=\delta_0^{d}\operatorname{vol}(\Lambda)^{1/d}$. The geometric series assumption models the Gram–Schmidt norms of a BKZ-reduced basis as decaying geometrically. Both enter concrete estimates of lattice attacks as modelling assumptions.

Let $B=(b_1,\dots,b_d)$ be a basis of a lattice $\Lambda$ of rank $d$, with Gram–Schmidt vectors $b_i^*$.

**Hermite and root-Hermite factor.** The Hermite factor of $B$ is $\|b_1\|/\operatorname{vol}(\Lambda)^{1/d}$, and the root-Hermite factor is the unique $\delta_0>0$ with

$$
\|b_1\| = \delta_0^{\,d}\,\operatorname{vol}(\Lambda)^{1/d}.
$$

**Geometric series assumption (GSA).** A basis satisfies the GSA if there is $0<\alpha<1$ with $\|b_i^*\| = \alpha^{\,i-1}\|b_1\|$ for $1\le i\le d$. It is Schnorr's assumption that the Gram–Schmidt norms of a BKZ-reduced basis decay geometrically, used for instance in Lindner and Peikert's analysis of decoding; it is not a consequence of being reduced.

**BKZ model.** Concrete estimates relate the root-Hermite factor achievable by BKZ with block size $\beta$ to $\beta$ by

$$
\delta_0=\Bigl(\frac{\beta}{2\pi e}\,(\pi\beta)^{1/\beta}\Bigr)^{1/(2(\beta-1))},
$$

which the HE Standard solves for $\beta$, following Chen's thesis. Chen and Nguyen report that the Gram–Schmidt norms of LLL- or BKZ-reduced bases of sufficiently randomized inputs typically have $\|b_i^*\|/\|b_{i+1}^*\|$ roughly constant except for the first indices, so that the Hermite factor is typically exponential in the dimension. Both are modelling assumptions and experimental observations, not theorems.

## Proof sketch

Combining the two definitions: if $d\ge2$ and the GSA holds with ratio $\alpha$, then $\prod_{i=1}^d\|b_i^*\|=\|b_1\|^d\alpha^{d(d-1)/2}$ equals $\operatorname{vol}(\Lambda)$, and $\|b_1\|^d=\delta_0^{d^2}\operatorname{vol}(\Lambda)$, so $\delta_0^{d^2}\alpha^{d(d-1)/2}=1$, i.e. $\alpha=\delta_0^{-2d/(d-1)}$. The $\delta_0(\beta)$ relation is recorded as the model the HE Standard uses; no claim about its accuracy is made.

## Depends on

- [The block Korkine–Zolotarev (BKZ) reduction algorithm](bkz-algorithm.md)

## Proof depends on

None.

## Sources

- Martin Albrecht, Melissa Chase, Hao Chen, Jintai Ding, Shafi Goldwasser, Sergey Gorbunov, Shai Halevi, Jeffrey Hoffstein, Kim Laine, Kristin Lauter, Satya Lokam, Daniele Micciancio, Dustin Moody, Travis Morrison, Amit Sahai, Vinod Vaikuntanathan, "Homomorphic Encryption Standard", version of November 21, 2018, HomomorphicEncryption.org, [https://homomorphicencryption.org/wp-content/uploads/2018/11/HomomorphicEncryptionStandardv1.1.pdf](https://homomorphicencryption.org/wp-content/uploads/2018/11/HomomorphicEncryptionStandardv1.1.pdf), Section 2.1.2: b. Primal by BDD enumeration (GSA, PDF p. 20), c. Dual (first vector of norm $\delta_0^m\operatorname{Vol}^{1/m}$, PDF p. 20) and Lattice Reduction algorithm: BKZ, a. Block Size (PDF p. 21).
- Yuanmi Chen, Phong Q. Nguyen, "BKZ 2.0: Better Lattice Security Estimates", ASIACRYPT 2011, Lecture Notes in Computer Science 7073, pp. 1–20, Springer, https://doi.org/10.1007/978-3-642-25385-0_1, Section 2 (Hermite factor and the typical shape of reduced Gram–Schmidt norms, p. 5).
