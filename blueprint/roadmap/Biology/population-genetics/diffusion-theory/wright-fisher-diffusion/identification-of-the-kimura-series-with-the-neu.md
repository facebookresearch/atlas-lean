# The neutral Gegenbauer series identifies the Wright–Fisher kernel

Let $K_t$ be the canonical [neutral Wright–Fisher kernel](../wright-fisher-semigroup-and-moment-duality/wf-transition-kernel.md)
on $[0,1]$, and let $p_t(x,y)$ be the
[uniformly convergent Gegenbauer series](kimura-1955-eigen-series-convergence-and-pde-for.md).
For $t>0$ and $x\in[0,1]$, define
$a_1(t,x)=x-\int_0^1y p_t(x,y)\,dy$ and
$a_0(t,x)=1-x-\int_0^1(1-y)p_t(x,y)\,dy$.
Then, as finite Borel measures on $[0,1]$,

$$K_t(x,dy)=p_t(x,y)\mathbf1_{(0,1)}(y)\,dy
+a_0(t,x)\delta_0(dy)+a_1(t,x)\delta_1(dy).$$

In particular the two atom masses are nonnegative, the displayed measure
has total mass one, and the continuous series is nonnegative pointwise
for $y\in[0,1]$. At $x=0,1$ the series vanishes and the kernel is the
corresponding endpoint point mass.
The density tends to zero uniformly in $x,y$ as $t\to\infty$; the atom
masses tend uniformly to $1-x$ and $x$, respectively.
This is a kernel-level identification. A pathwise killed-diffusion or
boundary-hitting-time interpretation is not asserted by this page alone.

## Depends on

- [Neutral transition kernel](../wright-fisher-semigroup-and-moment-duality/wf-transition-kernel.md)
- [Analytic Gegenbauer series and its uniform convergence](kimura-1955-eigen-series-convergence-and-pde-for.md)

## Proof depends on

- [Polynomial spectrum](../wright-fisher-diffusion-with-mutation/spectral-structure-of-l-0-theta-on-polynomials.md)
- [Linear Wright–Fisher semigroup](../wright-fisher-semigroup-and-moment-duality/wf-semigroup.md)
- [Polynomial semigroup derivative](../wright-fisher-semigroup-and-moment-duality/has-deriv-at-wf-semigroup-to-continuous.md)
- [Strong continuity at time zero](../wright-fisher-semigroup-and-moment-duality/tendsto-wf-semigroup-nhds-ge-zero.md)
- [Kernel representation of the semigroup](../wright-fisher-semigroup-and-moment-duality/integral-wf-transition-kernel.md)
- [Moment determinacy of compactly supported finite measures](../../../../Analysis/harmonic-analysis/integral-transforms/moment-problem-for-compactly-supported-measures/ext-of-forall-integral-pow-eq-of-compl-i.md)

## Expansion

Put $g(y)=y(1-y)$, $C_i(y)=C_{i-1}^{(3/2)}(1-2y)$,
$\varphi_i=gC_i$, $h_i=i(i+1)/(4(2i+1))$ and $\lambda_i=i(i+1)/2$.
The eigenfunction identity and semigroup linearity give, at every
positive time, $\frac d{dt}(T_t\varphi_i)(x)=-\lambda_i(T_t\varphi_i)(x)$.
Hence $e^{\lambda_i t}(T_t\varphi_i)(x)$ is constant on $(0,\infty)$.
Strong continuity as $t\downarrow0$ identifies that constant with
$\varphi_i(x)$. It follows that
$T_t\varphi_i=e^{-\lambda_i t}\varphi_i$; the same argument gives
$T_t1=1$ and $T_ty=y$. The derivative statement for positive times alone
would not determine these initial constants.

Every polynomial $f$ can be written
$f(y)=\alpha+\beta y+g(y)q(y)$, where $\alpha=f(0)$,
$\beta=f(1)-f(0)$ and $q$ is a polynomial. The polynomials $C_i$ have
successive degrees and nonzero leading coefficients, so $q=\sum_i c_iC_i$
with finitely many terms. Orthogonality gives
$c_i=h_i^{-1}\int_0^1g(y)q(y)C_i(y)\,dy$, zero beyond the finite degree.
Thus $(T_tf)(x)=\alpha+\beta x+\sum_i c_ie^{-\lambda_i t}\varphi_i(x)$.

Before positivity is known, call the right side of the displayed measure
formula $\nu$. It is a finite **signed** measure: $p_t(x,\cdot)$ is
continuous on a compact interval and the two atom coefficients are finite.
The definitions of $a_0,a_1$ give total mass one and first moment $x$.
Uniform convergence at this fixed positive time permits integration of
the density series against the bounded polynomial $gq$.
All higher coefficients vanish by orthogonality, giving
$\int f\,d\nu=\alpha+\beta x+\sum_i c_ie^{-\lambda_i t}\varphi_i(x)$.
The kernel representation therefore matches every polynomial integral.

The linked moment theorem is for nonnegative finite measures, so do not
apply it directly to $\nu$. Take its Jordan decomposition
$\nu=\nu^+-\nu^-$ and compare $K_t(x,\cdot)+\nu^-$ with $\nu^+$.
They are nonnegative finite measures with identical moments, supported
on $[0,1]$. Push them to $\mathbb R$ by the inclusion to apply the linked
compact-support theorem, then pull back along this injective inclusion.
It gives $K_t+\nu^-=\nu^+$ and hence $K_t=\nu$.
Positivity of the kernel gives the nonnegative atom masses and
nonnegativity of $p_t$ almost everywhere in the interior. Continuity
upgrades this to pointwise nonnegativity there and at its endpoints.
The uniform large-time density bound on the linked series page then
gives the stated atom limits.
In particular $\int_0^1p_t(x,y)\,dy=K_t(x,(0,1))$; identifying this
with a stopping-time survival probability still requires the relevant
process construction and boundary behavior.

## Sources

- M. Kimura, "Solution of a process of random genetic drift with a continuous model", Proceedings of the National Academy of Sciences USA 41 (1955), 144–150, <https://doi.org/10.1073/pnas.41.3.144>. The identification is derived above.
