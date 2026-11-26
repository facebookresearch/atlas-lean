# Nonuniqueness of global renormalized periodic hard-sphere Boltzmann flow

Use $z=(x,v)\in(\mathbb R/\mathbb Z)^3\times\mathbb R^3$ with unit spatial volume and Lebesgue velocity measure. For $w\in\mathbb R^3$, $\omega\in S^2$, take $b=|(v-w)\cdot\omega|$ and $v'=v-((v-w)\cdot\omega)\omega$, $w'=w+((v-w)\cdot\omega)\omega$. The collision gain and loss are the integrals of $bF(x,v')F(x,w')$ and $bF(x,v)F(x,w)$ over $dw\,d\omega$, using unnormalized sphere area. Write $Q=Q^+-Q^-$ and $M(v)=(2\pi)^{-3/2}e^{-|v|^2/2}$.

The claim is existence of one almost-everywhere nonnegative, essentially velocity-bounded initial density $f_0$ with integrable $f_0(1+|v|^2+|\log f_0|)$, and two global evolutions $F,G$ with that initial trace. For either evolution $F$:

- On $t\ge0$ it is jointly almost-everywhere strongly measurable; at every time it is almost-everywhere nonnegative and has the same finite-moment and measurability conditions as $f_0$ (but need not have bounded velocity support). Its moment integral is uniformly bounded on each finite time slab. $F(0)=f_0$ a.e., and integration against every bounded measurable phase test is continuous in $t\ge0$. Use $0|\log 0|=0$.
- The two collision integrands are integrable in $(w,\omega)$ at almost every phase-time in each finite slab. The separate gain and loss divided by $1+F/M$ are integrable on every finite slab.
- For each $C^1$ function $\beta$ on $[0,\infty)$ with $\beta(0)=0$ and $|\beta'(s)|\le C/(1+s)$, and each smooth spatially periodic test $\phi(t,x,v)$ of compact time and velocity support, the spacetime integrand below is integrable and satisfies

    $$
    \int_{t\ge0} [M\beta(F/M)(\partial_t+v\cdot\nabla_x)\phi+\beta'(F/M)Q\phi]\,dt\,dz
    +\int M\beta(f_0/M)\phi(0,x,v)\,dz=0.
    $$

    Use the right derivative of $\beta$ at zero. For every smooth spatially periodic time-compact $\psi(t,x)$, the analogous integrable transport identity holds with $F$ replacing $M\beta(F/M)$ and no collision term (local mass).
- At each $t\ge0$ the total momentum $\int v F(t)\,dz$ equals that of $f_0$ and $\int |v|^2 F(t)\,dz\le\int |v|^2 f_0\,dz$. The relative entropy $\int(F\log(F/M)-F+M)\,dz$ plus the time-integral from $0$ to $t$ of its nonnegative dissipation is at most the initial relative entropy. The dissipation is $\frac14\int b\,(A-B)\log(A/B)\,dx\,dv\,dw\,d\omega$ for $A=F(x,v')F(x,w')$, $B=F(x,v)F(x,w)$, continued by zero when both vanish and by $+\infty$ when exactly one vanishes.

There is a common $T>0$ on which both are strongly $L^1$ continuous on the closed interval $[0,T]$ and both **unrenormalized** collision gains and losses are spacetime integrable. At some $t\in[0,T]$ the two phase densities are not equal almost everywhere. This does not assert local momentum or local energy conservation. In the entropy inequality each real relative entropy is converted to an extended nonnegative real by taking its maximum with zero; the integrated dissipation is then added on the solution side. In the dissipation, the kernel multiplies the extended production with the convention $0\cdot(+\infty)=0$.

## Expansion

Separate construction of the collision integral from its integrable fibres and verify the signs and pre/post-collision change of variables. Formalize the transport and initial-trace identities, including the different test spaces for renormalization and local mass. Check that both constructions belong to this same admissibility class, preserve the stated global inequalities after extension, and give a strict early $L^1$ distinction.

## Sources

- OpenAI, [Comparator statement and definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BoltzmannNonuniqueness.lean#L19-L209) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/363.md).
- OpenAI, [Nonuniqueness for the periodic hard-sphere Boltzmann equation](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf) (September 23, 2026), accompanying preprint. The comparator above specifies the selected formal scope.
