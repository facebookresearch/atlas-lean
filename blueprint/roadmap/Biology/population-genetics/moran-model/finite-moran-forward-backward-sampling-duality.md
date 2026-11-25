# Finite neutral Moran sampling duality on the pair-coalescence clock

Fix $N\ge1$ gene copies. Start with the neutral ($r=1$) Moran step:
choose the reproducer and replaced individual independently and uniformly,
allowing self-replacement. Poissonize these steps at rate $N^2/2$.
The mutant count $X^{(N)}$ has generator $L_X$, with each of its two
possible jumps from an interior state $x$ occurring at rate $x(N-x)/2$;
$0,N$ are absorbing.

Let $A$ be the pure-death chain on $\{1,\ldots,N\}$ with rate
$\binom a2$ from $a$ to $a-1$ for $a\ge2$, and state $1$ absorbing.
It is the restriction of the canonical Kingman block-counting generator;
its additional state $0$ is unreachable from a positive start. For
$0\le x\le N$ and $1\le a\le N$, put

$$H_N(x,a)=\frac{\binom xa}{\binom Na}.$$

Here $\binom xa=0$ for $a>x$. The denominator is positive, and $H_N$
is the probability that a uniform sample of $a$ distinct individuals is
entirely mutant. For all $t\ge0$, $0\le x\le N$ and $1\le n\le N$,

$$\mathbb E_x H_N(X^{(N)}_t,n)=\mathbb E_n H_N(x,A_t).$$

For $n=1$, this gives preservation of the mean frequency; the Markov
property then gives
$\mathbb E[X^{(N)}_t/N\mid\mathcal F_s]=X^{(N)}_s/N$ for $0\le s\le t$
in the natural filtration. Boundedness supplies integrability.

The clock is exact, not just asymptotic: each ordered replacement has
rate $1/2$, and each specified unordered ancestral pair merges at rate
$1$. Equivalently, each unordered population pair has a rate-one clock
and a fair choice of replacement direction; self-events are null.
One unit of this time has $N^2/2$ original steps in expectation. With
$N$ original steps per generation, this is $N/2$ generations.
Calling every **ordered** replacement rate one would instead double
both generators.

## Depends on

- [One-step Moran probabilities](moran-prob.md)
- [Kingman block-counting generator](../../coalescent-theory/ancestral-lineage-counting-and-tavar-s-formula/block-counting-generator.md)

## Proof depends on

- [Exact neutral Moran ancestral partition kernel](moran-model-genealogy-per-step-c-2-n-2-and-time.md)
- [Truncation consistency of block-counting semigroups](../../coalescent-theory/ancestral-lineage-counting-and-tavar-s-formula/exp-smul-block-counting-generator-cast-l.md)
- [Kernel form of neutral Wright–Fisher moment duality](../diffusion-theory/wright-fisher-semigroup-and-moment-duality/integral-wf-transition-kernel-x-pow.md)

## Expansion

For an interior count $1\le x<N$ and $2\le a\le N$, Pascal's identity
gives the central second difference
$\binom{x+1}a+\binom{x-1}a-2\binom xa=\binom{x-1}{a-2}$.
The binomial recurrences then give

$$\frac{x(N-x)}2\frac{\binom{x-1}{a-2}}{\binom Na}
=\binom a2\left(\frac{\binom{x}{a-1}}{\binom{N}{a-1}}
-\frac{\binom xa}{\binom Na}\right).$$

At $x=0,N$, both generators applied to $H_N$ give zero, since its
corresponding rows are constant zero and one. For $a=1$, the column
$x/N$ is linear and both generator actions are zero. These separate
cases avoid undefined negative-index binomials and evaluation outside
the count state space. They include the trivial case $N=1$.

Using row-generator conventions, the identity is
$L_XH_N=H_NL_A^{\mathsf T}$. Induction gives
$L_X^kH_N=H_N(L_A^{\mathsf T})^k$ for every $k$.
Absolute convergence of the finite-matrix exponential series therefore
gives $e^{tL_X}H_N=H_Ne^{tL_A^{\mathsf T}}$, which is the stated duality.

For the genealogy identification, the exact discrete partition kernel
merges each specified pair with probability $2/N^2$ per step, independently
of the labels and entire previous ancestral history. Multiplication by
the Poisson rate $N^2/2$ gives rate one for each pair and hence total
death rate $\binom a2$. The linked argument covers $N\ge2$; $N=1$
is constant. Neutrality and the permitted self-events are part of this
model, not omitted normalization choices.

To make the diffusion comparison precise, fix $n\ge1$, let $N\to\infty$
with $N\ge n$, and choose integers $x_N$ with $0\le x_N\le N$ and
$x_N/N\to p\in[0,1]$. Sampling labels with replacement and conditioning
on no repeated label gives the uniform bound

$$\left|H_N(x,n)-(x/N)^n\right|
\le 1-\frac{(N)_n}{N^n}\le\frac{\binom n2}{N},$$

where $(N)_n=N(N-1)\cdots(N-n+1)$. The last step is the union bound
for a collision among $n$ independently sampled labels. Thus
$H_N(x_N,k)\to p^k$ for every $1\le k\le n$.
Since the death chain started at $n$ stays in $\{1,\ldots,n\}$, truncation
consistency makes its law independent of $N\ge n$. The finite duality
and the uniform bound now imply, for each fixed $t\ge0$,

$$\lim_{N\to\infty}\mathbb E_{x_N}(X^{(N)}_t/N)^n
=\sum_{k=1}^n(e^{tG_n})_{nk}p^k
=\int y^n\,K_t(p,dy).$$

The last equality is the existing neutral Wright–Fisher kernel theorem,
with generator $\tfrac12p(1-p)\partial_{pp}$. This establishes the
fixed-order, fixed-time moment limit on the stated clock; it does not
infer convergence of forward processes merely from convergence of the
sampling function, or assert path-space convergence.

## Sources

- P. Donnelly, "The transient behaviour of the Moran model in population genetics", *Mathematical Proceedings of the Cambridge Philosophical Society* 95(2) (1984), 349–358, <https://doi.org/10.1017/S0305004100061624>. The finite identity, normalization and moment comparison above are derived using the linked canonical contracts.
