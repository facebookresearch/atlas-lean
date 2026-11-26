# Normalized cubic Gauss sums at primary Eisenstein primes

Let $\omega=e^{2\pi i/3}$ and $O=\mathbb Z[\omega]$ in its given complex embedding. Sum over prime
**elements** $p\in O$ satisfying $p\equiv1\pmod{3O}$; do not select only one per conjugate pair.
Write $N(p)=|p|^2$. On each residue $v\in O/(p)$ let $\chi_p(v)=0$ at nonunits, and on units
let $\chi_p(v)$ be the complex cube root $\omega^j$ whose reduction equals $v^{(N(p)-1)/3}$.
The source takes the natural floor of the norm (which is integral for $O$), natural division in the
exponent, and assigns zero in the unit case if no such root exists. For such a prime, the defining
sum is

$$
G(p)=\frac1{\sqrt{N(p)}}\sum_{v\bmod p}\chi_p(v)
 \exp\!\left(2\pi i\left(\frac{\widetilde v}{p}+\overline{\frac{\widetilde v}{p}}\right)\right),
$$

using any integral lift $\widetilde v$ of each residue. This additive phase uses the trace, not just
the real part. Write $\theta_\ell(p)=(p/|p|)^\ell$ for an integer $\ell$ (negative exponents allowed)
and $c_*=(2\pi)^{2/3}/(3\Gamma(2/3))$.

## Expansion

Identify the integral and residue norm for the complex Eisenstein ring; prove that the cubic roots are distinct modulo each primary prime and that the trace phase is independent of the lift. Justify treating the source’s sums of finite support as finite sums, both over residues and over norm cutoffs.

## Sources

- [PattersonFirstMoment.lean — `patterson_firstMoment`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PattersonFirstMoment.lean#L83-L86)
- [PattersonFirstMoment.lean — `patterson_angularComparison`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PattersonFirstMoment.lean#L87-L90)
- [PattersonFirstMoment.lean — `patterson_angularCancellation`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PattersonFirstMoment.lean#L91-L94)
- [Source Eisenstein ring, Gauss sum and angular mode](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PattersonFirstMoment.lean#L16-L81)
