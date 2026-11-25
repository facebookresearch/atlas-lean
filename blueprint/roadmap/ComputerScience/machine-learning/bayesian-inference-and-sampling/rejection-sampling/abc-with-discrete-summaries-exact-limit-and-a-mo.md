# ABC with discrete summaries: exactness at small tolerance and a model-choice counterexample

1. *Exactness below the gap.* Let the summary $S$ take values in a separable metric space $(\mathcal S,d)$, let $\nu$ be its law under the prior predictive distribution, and let $s_{\rm obs}$ be an isolated point of the support of $\nu$ (for instance, $S$ has finite support). Then $\nu(\{s_{\rm obs}\})>0$,

$$\gamma=\inf\{d(s,s_{\rm obs}):s\in\operatorname{supp}\nu,\ s\ne s_{\rm obs}\}>0$$

(with $\gamma=\infty$ if $\operatorname{supp}\nu=\{s_{\rm obs}\}$), and for every tolerance $0\le\varepsilon<\gamma$ the [rejection ABC target](abc-rejection-target-law-and-zero-tolerance-disc.md) $\pi_\varepsilon$ equals the posterior given $S=s_{\rm obs}$.

2. *Within-model sufficiency does not give the right Bayes factor.* Let $x=(x_1,\ldots,x_n)\in\mathbb N_0^n$ be observed, and compare model 1, $x_i$ independent $\operatorname{Poisson}(\lambda)$, with model 2, $x_i$ independent geometric on $\{0,1,2,\ldots\}$ with $P(x_i=k)=p(1-p)^k$, each with a proper prior on its parameter. The sum $S=\sum_ix_i$ is sufficient within each model, and given $S=s$ the data are multinomial $(s;\tfrac1n,\ldots,\tfrac1n)$ under model 1 and uniform on the $\binom{s+n-1}{n-1}$ compositions of $s$ under model 2. Hence the full-data Bayes factor $B_{12}(x)$ and the Bayes factor $B_{12}^S(x)$ based on $S$ alone satisfy

$$B_{12}(x)=B_{12}^S(x)\cdot\frac{s!}{\prod_ix_i!\;n^{s}}\binom{s+n-1}{n-1},\qquad s=\sum_ix_i,$$

for every choice of the two priors. For $n=2$ and $x=(2,0)$ the factor is $\tfrac14\cdot3=\tfrac34$, so $B_{12}\ne B_{12}^S$. By part 1, zero-tolerance ABC model choice on $S$ (an integer-valued summary) targets $B_{12}^S$, not $B_{12}$.

## Depends on

- [Rejection ABC returns the tolerance-conditioned posterior](abc-rejection-target-law-and-zero-tolerance-disc.md)

## Proof depends on

- [Prokhorov's theorem, sequential form on $\mathbb{R}$](../../../../Probability/convergence-of-measures/prokhorov-theorem/prokhorov-sequential.md)

## Expansion

A full proof page must establish:

- Part 1: an isolated support point of a Borel probability measure on a separable metric space is an atom; the gap $\gamma$ is positive; for $\varepsilon<\gamma$ the acceptance event $\{d(S,s_{\rm obs})\le\varepsilon\}$ equals $\{S=s_{\rm obs}\}$ up to a $\nu$-null set, so the acceptance probabilities and the ABC target coincide with those at $\varepsilon=0$.
- Part 2: the two conditional laws of the data given $S$, the factorization of each marginal likelihood as (marginal likelihood of $S$) times (conditional probability of $x$ given $S$), which does not involve the parameter, and the numerical case $n=2$, $x=(2,0)$.

## Sources

- P. Fearnhead and D. Prangle, *Constructing summary statistics for approximate Bayesian computation: semi-automatic approximate Bayesian computation*, Journal of the Royal Statistical Society Series B (2012) (summary construction; background).
- C. P. Robert, J.-M. Cornuet, J.-M. Marin and N. S. Pillai, *Lack of confidence in approximate Bayesian computation model choice*, Proceedings of the National Academy of Sciences (2011) (the model-choice caveat).
