# Count-sampled and position-sampled ancestry tract lengths

In the stationary [Poisson-relabeling model](poisson-switch-markov-model-of-local-ancestry-al.md),
let $T>0$ and $0<\alpha<1$. A tract is a maximal interval of one ancestry,
not an interval between arbitrary candidate points.
An $A$ tract sampled by its start point (the stationary count/Palm law)
has length $L_A\sim\operatorname{Exp}(\lambda_A)$, with
$\lambda_A=(1-\alpha)T$. Similarly
$L_B\sim\operatorname{Exp}(\lambda_B)$ with $\lambda_B=\alpha T$.
The intensity of $A$-tract starts is $\alpha(1-\alpha)T$ per Morgan,
and the total ancestry-change intensity is twice this.

At a fixed genomic position, conditional on ancestry $A$, the length of
the entire containing tract instead has density
$\lambda_A^2\ell e^{-\lambda_A\ell}$ for $\ell>0$, namely
$\operatorname{Gamma}(2,\text{rate }\lambda_A)$.
Its mean is $2/\lambda_A$, twice the count-sampled mean.

## Depends on

- [Stationary Poisson-relabeling ancestry model](poisson-switch-markov-model-of-local-ancestry-al.md)

## Expansion

Starting at an $A$-tract entry, the number $K$ of candidate segments until
a $B$ label has law $\mathbb P(K=k)=\alpha^{k-1}(1-\alpha)$.
The segment lengths are independent rate-$T$ exponentials. Their sum has
Laplace transform, for $s\ge0$,

$$\sum_{k\ge1}(1-\alpha)\alpha^{k-1}
 \left(\frac{T}{T+s}\right)^k
 =\frac{(1-\alpha)T}{(1-\alpha)T+s},$$

or, directly, the first retained $B$ mark occurs with rate $(1-\alpha)T$.
Stationary $B\to A$ flux is $(1-\alpha)\alpha T$.
A position weights tracts in proportion to length, turning the density
$\lambda_Ae^{-\lambda_A\ell}$ into
$\ell\lambda_Ae^{-\lambda_A\ell}/\mathbb E L_A
=\lambda_A^2\ell e^{-\lambda_A\ell}$.
Equivalently, conditional on the label at zero, the backward and forward
distances to the tract endpoints are independent rate-$\lambda_A$
exponentials in the stationary two-state reversible chain.

The number of $A$ tracts intersecting a window of length $L$ has mean
$\alpha+L\alpha(1-\alpha)T$; this includes a possible left-edge tract,
whereas the start-count intensity does not. Finite-window censored lengths
need not have the untruncated exponential law. As $\alpha\to1$, the
$A$-tract mean diverges. At $\alpha=1$ the whole line is one unbounded
$A$ tract; an exponential law with rate zero is not a probability law.
At $\alpha=0$ there are no $A$ tracts to sample.

## Sources

- S. Gravel, *Population genetics models of local ancestry* (2012), <https://doi.org/10.1534/genetics.112.139808>, <https://arxiv.org/abs/1202.4811>, equation (1). Its exposure is $t-1$. Count-versus-position sampling and the boundary/window qualifications are derived here.
