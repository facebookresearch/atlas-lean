# A zero-free half-plane for finite-order Hecke L-functions over the Eisenstein field

Let $K=\mathbb Q(\omega)$ with $\omega$ a primitive cube root of unity, and $O=\mathbb Z[\omega]$.
Take a nonzero ideal $\mathfrak m$ of $O$, a complex multiplicative residue character $\chi$ modulo
$\mathfrak m$ trivial on the units of $O$, and a positive integer $N\in\mathfrak m$ as an additive
period in both integral coordinates. The residue character is zero on nonunit classes. Write
$w(a,b)=\chi(a+b\omega\bmod\mathfrak m)$ for $0\le a,b<N$ and use the embedding
$\omega=(-1+i\sqrt3)/2$. For $t>0$ the weighted theta kernel is

$$
f(t)=\sum_{x,y\in\mathbb Z} w(x\bmod N,y\bmod N)e^{-\pi t(x^2-xy+y^2)}.
$$

The two constants of the assembled weak functional-equation pair of weight $1$ and multiplier $1$ are
$f_0=w(0,0)$ and $g_0=\frac{2}{\sqrt3\,N^2}\sum_{0\le a,b<N}w(a,b)$. In the source, $f_0$ comes
from the zero lattice element; $g_0$ is the sum of the constant terms in the dual parity kernels.
Define $f_{\mathrm{reg}}(t)=f(t)-f_0$ for $t>1$, $f_{\mathrm{reg}}(t)=f(t)-g_0/t$ for $0<t<1$,
and $f_{\mathrm{reg}}(1)=0$. The source's completed and uncompleted functions are

$$
\Lambda(s)=\int_0^\infty f_{\mathrm{reg}}(t)t^{s-1}\,dt-\frac{f_0}{s}-\frac{g_0}{1-s},
\qquad L(s,\chi)=\frac{\pi^s}{6}\,\Gamma(s)^{-1}\Lambda(s).
$$

For $\operatorname{Re}s>1$, $\Lambda$ agrees with the Mellin transform of $f-f_0$, not of $f$.
Consequently the Dirichlet-series normalization on that half-plane is

$$
L(s,\chi)=\frac16\sum_{z\in O\setminus\{0\}}\chi(z\bmod\mathfrak m)\,|z|^{-2s}.
$$

In the pointwise source formula division by zero is totalized; in the theorem the pair consisting of
principal $\chi$ and $s=1$ is explicitly excluded. For every other pair with $\operatorname{Re}s>7/8$,
$L(s,\chi)\ne0$. The target concerns this explicit lattice continuation. Comparison with the
adelic $L$-function is separate and must account for omitted Euler factors at primes dividing the
chosen modulus.

## Expansion

Derive the two rescaled even Hurwitz theta kernels for each parity by splitting $(2x-y)^2+3y^2=4|x+y\omega|^2$. Check both constant terms (including the unit ideal and period one), their rescaling factors, and the exact $\Lambda$ regularization. Verify the lattice sum agrees with the residue character ideal-series normalization, independent of $N$, before identifying any adelic model; include the omitted Euler factors, the units factor of six, and the principal pole. Separate the weak-pair model and its Mellin comparison from the certified-band nonvanishing estimates.

## Sources

- [HeckeSevenEighths.lean — `LFunction_ne_zero_of_seven_eighths_lt_re`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HeckeSevenEighths.lean#L237-L240)
- [Source theta construction and weak functional-equation pair](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HeckeSevenEighths.lean#L18-L202)
- [Source residue model and uncompletion](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HeckeSevenEighths.lean#L206-L239)
- [Mathlib weak FE-pair modification](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean#L246-L251)
- [Mathlib meromorphic Mellin transform](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean#L376-L408)
