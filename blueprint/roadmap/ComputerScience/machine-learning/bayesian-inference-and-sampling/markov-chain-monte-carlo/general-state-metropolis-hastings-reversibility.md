# Metropolis–Hastings with densities is reversible

Let $E$ be a standard Borel space with sigma-finite reference measure
$\lambda$. Let $p:E\to[0,\infty)$ and $q:E\times E\to[0,\infty)$ be
finite, measurable densities, with $\int p\,d\lambda=1$ and
$\int q(x,y)\,\lambda(dy)=1$ for each $x$.
Write $\pi(dx)=p(x)\lambda(dx)$ and $Q(x,dy)=q(x,y)\lambda(dy)$.
Set $a(x,y)=p(x)q(x,y)$, and define
$\alpha(x,y)=\min(1,a(y,x)/a(x,y))$ when $a(x,y)>0$, and
$\alpha(x,y)=1$ when $a(x,y)=0$. Then

$$P(x,dy)=\alpha(x,y)Q(x,dy)
 +\left(1-\int\alpha(x,z)Q(x,dz)\right)\delta_x(dy)$$

is a Markov kernel and is reversible for $\pi$:
$\pi(dx)P(x,dy)=\pi(dy)P(y,dx)$. In particular $\pi P=\pi$.
No positivity of the target or proposal on all pairs is required.

## Background

- [Canonical discrete Metropolis–Hastings detailed balance](mh-detailed-balance.md)

## Expansion

Measurability and $0\le\alpha\le1$ make the displayed formula a
probability kernel. On every pair, including zero-density cases,
$a(x,y)\alpha(x,y)=\min(a(x,y),a(y,x))$.
Thus the accepted part of $\pi(dx)P(x,dy)$ has symmetric density with
respect to $\lambda\otimes\lambda$. The rejection part is the pushforward
of $p(x)(1-\int\alpha Q)\lambda(dx)$ under $x\mapsto(x,x)$, hence is
symmetric too. This argument includes atoms and accepted self-proposals;
it does not assume the diagonal has zero reference measure.
Integrating out the first coordinate proves invariance.
For counting measure it specializes to the linked discrete theorem.

Reversibility does not imply convergence from every initial state or
independent target samples. An identity proposal leaves every state fixed
while still satisfying detailed balance for any target. Irreducibility,
aperiodicity and any quantitative convergence guarantees are separate.

## Sources

- C. Andrieu and G. O. Roberts, *The pseudo-marginal approach for efficient Monte Carlo computations*, Annals of Statistics 37 (2009), 697–725, <https://doi.org/10.1214/07-AOS574>, <https://arxiv.org/abs/0903.5480>, equations (2.5)–(2.6) for the marginal MH kernel and acceptance convention. The density and rejection-measure proof is explicit above.
