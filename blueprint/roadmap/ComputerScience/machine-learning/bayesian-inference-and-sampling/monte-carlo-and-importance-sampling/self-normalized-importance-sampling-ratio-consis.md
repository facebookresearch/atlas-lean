# Consistency of self-normalized importance sampling and the range of the effective sample size

Let $\pi,q$ be probability measures on a measurable space, with $\pi\ll q$,
and let $\gamma=Z\pi$, where $0<Z<\infty$. Choose a measurable, finite,
nonnegative version $w$ of $d\gamma/dq$; this is possible because the
derivative is finite $q$-almost everywhere. Let $(X_i)_{i\ge0}$ be measurable,
independent samples with common law $q$. For each fixed measurable
$f:\alpha\to\mathbb R$ integrable under $\pi$, and integer $n\ge1$, set
$S_n=\sum_{i<n}w(X_i)$ and define

$$\widehat\pi_n(f)=
\begin{cases}
\displaystyle\frac{\sum_{i<n}w(X_i)f(X_i)}{S_n},&S_n>0,\\
0,&S_n=0.
\end{cases}$$

Then $\widehat\pi_n(f)\to\int f\,d\pi$ almost surely.
In fact $S_n/n\to Z$, so $S_n>0$ eventually almost surely. The chosen
value on zero-denominator prefixes therefore does not affect consistency.
No second moment of $w$ or boundedness of $f$ is required for this claim.
The almost-sure event may depend on the fixed observable $f$.

For any finite nonnegative weights $w_0,\ldots,w_{n-1}$ with $S=\sum_iw_i>0$,
define $\operatorname{ESS}=S^2/\sum_iw_i^2$. Then $1\le\operatorname{ESS}\le n$.
Equality at $n$ holds exactly when all the weights are equal, necessarily
to a positive value; equality at $1$ holds exactly when one weight is
positive. This is a deterministic finite-weight statement, not an assertion
that ESS is an observable-independent variance reduction factor.

If $q=\pi$, then $w=Z$ $q$-almost everywhere, not necessarily at every point
for an arbitrary derivative version. Almost surely all sampled weights
are $Z$, so for every $n\ge1$ the estimator is the ordinary sample mean,
its expectation is $\int f\,d\pi$, and ESS is $n$. The probability-target
weights $w/Z$ are one; the empirical normalized weights are $1/n$.

## Depends on

- [Importance-sampling estimate](is-estimate.md)
- [Change of measure for importance weights](integral-weight-mul.md)

## Proof depends on

- [Consistency of ordinary importance sampling](tendsto-is-estimate.md)
- [Unbiasedness of the Monte Carlo estimate](integral-mc-estimate.md)

## Expansion

The numerator divided by $n$ is the existing ordinary importance estimate
of $f$ for target $\gamma$; the denominator divided by $n$ is that of $1$.
Change of measure gives $\int w\,dq=Z$ and
$\int|wf|\,dq=Z\int|f|\,d\pi<\infty$.
The existing consistency theorem, applied to these two observables and
intersecting their two probability-one events, yields limits
$Z\int f\,d\pi$ and $Z$. Eventually $S_n/n>Z/2$, so the quotient limit
applies on that event. This reuses the ordinary-importance theorem rather
than creating a second implementation of its strong law.

For the ESS identities put $Q=\sum_iw_i^2$. Positivity of $S$ gives $Q>0$,
and

$$S^2-Q=2\sum_{i<j}w_iw_j\ge0,
\qquad nQ-S^2=\sum_{i<j}(w_i-w_j)^2\ge0.$$

The equality conditions follow term by term. If $q=\pi$, uniqueness of the
Radon–Nikodym derivative gives $w=Z$ almost everywhere. A countable union
of null events makes this hold simultaneously for all sample indices;
then cancel $Z$ and reuse sample-mean unbiasedness.

Zero-weight prefixes can really occur: with $q$ uniform on $\{a,b\}$,
$\pi=\delta_a$, and $Z=1$, the weights are $2,0$ and
$\Pr(S_n=0)=2^{-n}$. Thus positivity for every finite sample is not a
consequence of absolute continuity alone.

A separate quantitative target is the $O(\rho/n)$ bias and mean squared
error bound for bounded $f$, where $\rho=\mathbb E_q[w^2]/Z^2<\infty$.
Its explicit constants, hypotheses and zero-denominator convention must
be checked against the primary source before that result is admitted.
This page establishes consistency and ESS bounds, not those quantitative
bounds.

## Background

- [Strong law via the ergodic theorem](../../../../Dynamics/ergodic-theory/birkhoff-ergodic-theorem/tendsto-average-coordinates-ae.md): applying it to $wf$ and $w$ under the iid product law gives the same two limits.

## Sources

- S. Agapiou, O. Papaspiliopoulos, D. Sanz-Alonso and A. M. Stuart, "Importance Sampling: Intrinsic Dimension and Computational Cost", *Statistical Science* 32(3) (2017), 405–431, <https://doi.org/10.1214/17-STS611>. The consistency and ESS arguments above are derived using the linked canonical results.
