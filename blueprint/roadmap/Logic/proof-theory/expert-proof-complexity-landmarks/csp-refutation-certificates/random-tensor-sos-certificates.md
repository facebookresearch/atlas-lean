# Sum-of-squares certificates for the maximum of a random tensor on the sphere

For a random $\pm1$ tensor of order $d$, degree-$q$ sum-of-squares certifies an upper bound on its maximum over the unit sphere within a factor $(\tilde{O}(n)/q)^{d/4-1/2}$ of the true value, and for $q=d$ this factor $(n/q)^{q/4-1/2}$ is tight up to $2^{O(q)}$: the relaxation value is that far above the maximum.

For an order-$d$ tensor $\mathcal{A}\in(\mathbb{R}^n)^{\otimes d}$ write $\mathcal{A}(x)=\langle\mathcal{A},x^{\otimes d}\rangle$ and $\mathcal{A}_{\max}=\sup_{\|x\|_2=1}\mathcal{A}(x)$. A degree-$q$ pseudo-expectation ($q$ even) is a linear map $\tilde{\mathbb{E}}$ on real polynomials of degree at most $q$ in $x_1,\dots,x_n$ with $\tilde{\mathbb{E}}[1]=1$ and $\tilde{\mathbb{E}}[p^2]\ge0$ for every $p$ of degree at most $q/2$; it respects the constraint $\|x\|_2^q=1$ if $\tilde{\mathbb{E}}[p\cdot(\|x\|_2^q-1)]=0$ for every $p$ with $\deg(p\cdot(\|x\|_2^q-1))\le q$. The **degree-$q$ SoS relaxation** $\mathrm{SoS}_q(\mathcal{A}(x))$ is the maximum of $\tilde{\mathbb{E}}[\mathcal{A}(x)]$ over degree-$q$ pseudo-expectations respecting $\|x\|_2^q=1$; it satisfies $\mathcal{A}_{\max}\le\mathrm{SoS}_q(\mathcal{A}(x))$ and is computable by a semidefinite program of size $n^{O(q)}$. For i.i.d. Rademacher entries, $\mathcal{A}_{\max}\lesssim\sqrt{n\cdot d\cdot\log d}$.

**Theorem (SoS degree equal to tensor order).** For every even $q\le n$, let $\mathcal{A}\in(\mathbb{R}^n)^{\otimes q}$ have independent Rademacher entries. With high probability (failure probability $n^{-\Omega(1)}$),

$$
2^{-O(q)}\cdot\left(\frac{n}{q}\right)^{q/4-1/2}\le\frac{\mathrm{SoS}_q(\mathcal{A}(x))}{\mathcal{A}_{\max}}\le2^{O(q)}\cdot\left(\frac{n}{q}\right)^{q/4-1/2},
$$

and in the explicit form proved in the body,

$$
\left(\frac{\Omega(n)}{q}\right)^{q/4-1/2}\le\frac{\mathrm{SoS}_q(\mathcal{A}(x))}{\mathcal{A}_{\max}}\le\left(\frac{O(n)}{q}\right)^{q/4-1/2}.
$$

**Theorem (SoS degree above tensor order).** Let $\mathcal{A}\in(\mathbb{R}^n)^{\otimes d}$ have independent Rademacher entries. For every even $q$ with $d\le q\le n$, with high probability degree-$q$ SoS certifies an upper bound $B$ on $\mathcal{A}_{\max}$ with

$$
\frac{B}{\mathcal{A}_{\max}}\le\left(\frac{\tilde{O}(n)}{q}\right)^{d/4-1/2}.
$$

For even $d$ this holds with $B=\mathrm{SoS}_q(\mathcal{A}(x))$ for every even $q\le n$, with probability $1-n^{-\Omega(1)}$; for $d=3$ the bound reads $(\tilde{O}(n)/q)^{1/4}$.

## Expansion

The dual of the relaxation for a homogeneous polynomial $g$ of even degree $t$ is $\Lambda(g)=\inf\lambda_{\max}(M_g)$ over matrix representations $g(x)=(x^{\otimes t/2})^{\mathsf T}M_gx^{\otimes t/2}$, and pseudo-Cauchy-Schwarz gives $\mathcal{A}_{\max}\le\mathrm{SoS}_q(\mathcal{A}(x))\le\Lambda(\mathcal{A}(x)^{q/d})^{d/q}$ when $2d$ divides $q$. The upper bound picks a suitable matrix representation $M$ of $\mathcal{A}(x)^{q/d}$ built from the flattening $A[I,J]=\mathcal{A}[I\oplus J]$ and bounds $\|M\|_2\le\tilde{O}_d\big((n\log^5n/q^{1-2/d})^{q/4}\big)$ by the trace moment method; each such spectral bound is a degree-$q$ sum-of-squares proof that $\mathcal{A}(x)$ is at most $B$ on the sphere. Odd $d$ uses the decomposition $\mathcal{A}(x)=\sum_\ell x_\ell(x^{\mathsf T}T_\ell x)$. The lower bound constructs, starting from an SoS-symmetrized analogue of the identity matrix, a positive semidefinite, SoS-symmetric moment matrix $\mathsf{M}$ of trace $1$ with $\langle A,\mathsf{M}\rangle\ge2^{-O(q)}n^{q/4}/q^{q/4}$; it defines a pseudo-expectation whose value exceeds the true maximum by the stated factor. Raghavendra, Rao and Schramm obtained the analogous certificates for sparse random polynomials, which give the sub-exponential-time refutation of random CSPs that the [smoothed CSP refutation theorem](smoothed-csp-refutation.md) extends to worst-case scopes.

## Depends on

None.

## Proof depends on

None.

## Sources

- Vijay Bhattiprolu, Venkatesan Guruswami, Euiwoong Lee, "Sum-of-Squares Certificates for Maxima of Random Tensors on the Sphere", *APPROX/RANDOM 2017* (RANDOM 2017, LIPIcs), 2017, arXiv:1605.00903v2, https://arxiv.org/abs/1605.00903 (Theorems 1.1 and 1.2; Definitions 2.2 and 2.3; Section 2.2 for the relaxation; Theorem 4.4; Theorems 5.7 and 5.8; Theorem A.5).
