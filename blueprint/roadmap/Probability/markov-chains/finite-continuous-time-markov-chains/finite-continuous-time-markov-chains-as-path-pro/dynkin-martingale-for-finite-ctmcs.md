# Dynkin martingale of a finite continuous-time Markov chain

Let $Q$ be a rate matrix on a finite nonempty state set $S$, and take
its canonical [path process](ctmc-path.md) under any initial probability
law, with natural filtration $\mathcal F_t=\sigma(X_u:0\le u\le t)$.
For every $f:S\to\mathbb R$,

$$M_t=f(X_t)-f(X_0)-\int_0^t(Qf)(X_u)\,du$$

is an integrable real martingale. This is the martingale problem for
$Q$ with all real functions on the finite state set as test functions.
No separate general definition of martingale problems is needed to interpret
this explicitly stated property.

## Depends on

- [Finite-state continuous-time path](ctmc-path.md)

## Proof depends on

- [Full finite-dimensional distributions](ctmc-input-measure-real-ctmc-path-fdd.md)
- [Joint measurability of the path](measurable-ctmc-path-uncurry.md)
- [Kolmogorov backward equation](../the-transition-semigroup-of-a-finite-continuous/has-deriv-at-ctmc-transition-backward.md)

## Expansion

The finite-dimensional product law, applied on a grid containing $s,t$
and finitely many times before $s$, gives
$\mathbb E[f(X_t)\mid\mathcal F_s]=(e^{(t-s)Q}f)(X_s)$ after a
monotone-class argument on past cylinders. The fixed-time restart law
that only joins $X_s$ to its future would not by itself justify this
conditioning on the entire past.
Joint measurability and boundedness of $Qf$ justify conditional Fubini
on $[s,t]$. Since $Q$ commutes with its exponential, the backward equation
gives

$$e^{(t-s)Q}f-f=\int_s^t e^{(u-s)Q}Qf\,du.$$

Subtract the two conditional expressions to obtain
$\mathbb E[M_t-M_s\mid\mathcal F_s]=0$. Bounded state functions and finite
time integrals give integrability and adaptation.
For a neutral Moran count chain on $\{0,\ldots,M\}$, $M\ge1$, with
equal upward and downward rates at each interior count and absorbing
endpoints, $f(i)=i/M$ satisfies $Qf=0$. Its frequency process is therefore
a bounded martingale, independently of the common choice of clock scale.

## Sources

- Derived from the canonical finite-dimensional path law and matrix-exponential equation as shown above. The two-time restart identity is deliberately not substituted for a natural-filtration Markov property.
