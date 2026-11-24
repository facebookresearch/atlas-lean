# Reversibility of the Moran origination–fixation rate model

Let $G$ be a finite nonempty genotype set, $N\ge1$ an integer,
$\mu\ge0$, and $f(g)>0$. Let $m(g,h)=m(h,g)\ge0$ for distinct
$g,h$. Define the **off-diagonal** rates

$$q(g,h)=N\mu m(g,h)\varphi(f(h)/f(g))\quad(g\ne h),
\qquad q(g,g)=-\sum_{h\ne g}q(g,h),$$

where the canonical [single-mutant Moran probability](../population-genetics/moran-model/moran-fixation.md)
is $\varphi(r)=(1-r^{-1})/(1-r^{-N})$ for $r\ne1$ and
$\varphi(1)=1/N$. For every $r>0$,
$\varphi(r)/\varphi(1/r)=r^{N-1}$.
Hence this rate matrix satisfies [detailed balance](../../Probability/markov-chains/finite-continuous-time-markov-chains/stationarity-and-detailed-balance-for-finite-con/is-detailed-balance.md)
with the probability vector

$$\pi(g)=\frac{f(g)^{N-1}}{\sum_{h\in G}f(h)^{N-1}}.$$

It is stationary and is the unique stationary law when the rate graph
is irreducible. For equal fitnesses it is uniform; when $N=1$ it is
uniform even for unequal fitnesses. If $\mu=0$, every distribution is
stationary, so uniqueness is not asserted except on a singleton.

## Depends on

- [Moran fixation probability](../population-genetics/moran-model/moran-fixation.md)
- [Detailed balance for a real matrix](../../Probability/markov-chains/finite-continuous-time-markov-chains/stationarity-and-detailed-balance-for-finite-con/is-detailed-balance.md)

## Expansion

The geometric-sum form $\varphi(r)=1/\sum_{j=0}^{N-1}r^{-j}$ is valid
also at $r=1$ and is positive. Reversing the finite sum proves the ratio
identity, including the neutral and $N=1$ cases. It gives
$f(g)^{N-1}\varphi(f(h)/f(g))
=f(h)^{N-1}\varphi(f(g)/f(h))$, and symmetry of $m$ gives detailed
balance. Row sums and that identity imply $\pi Q=0$.
For uniqueness, if $\nu Q=0$, detailed balance makes
$z_g=\nu(g)/\pi(g)$ harmonic for $Q$.
At a maximum of $z$, the nonnegative off-diagonal rates force every
neighbor to have the same value; irreducibility propagates this to all
states. Normalization then gives $\nu=\pi$.

The rate model assumes a monomorphic population between successful
substitutions. The algebra proves reversibility **of this specified
chain**, not convergence of a finite-mutation population process to it.

## Sources

- G. Sella and A. E. Hirsh, "The application of statistical physics to evolutionary biology", Proceedings of the National Academy of Sciences USA 102 (2005), 9541–9546, <https://doi.org/10.1073/pnas.0501865102>. The identity is derived above.
