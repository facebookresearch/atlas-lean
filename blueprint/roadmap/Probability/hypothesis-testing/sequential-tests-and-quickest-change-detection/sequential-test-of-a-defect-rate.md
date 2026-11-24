# Sequential test of a defect rate

Let $\alpha,q\in(0,1)$. On $\Omega=\mathbb{N}^{\mathbb{N}}$ with its product sigma-algebra, let $P_\theta$ be the product of
Bernoulli count laws with parameter $\theta\in(0,1)$, and let $X_i$ be coordinate $i$. These coordinates are independent,
strongly measurable and binary almost surely under each $P_\theta$, not on every path in $\Omega$. Use their natural filtration.
Define the total likelihood-ratio factor by

$$L_\theta(k)=\begin{cases}q/\theta&k=1,\\(1-q)/(1-\theta)&k=0,\\0&k\notin\{0,1\},\end{cases}
\qquad E_n^\theta=\prod_{i=0}^n L_\theta(X_i),\quad n\ge0.$$

On almost every path this is the usual product of binary Bernoulli likelihood ratios. In particular $E_0^\theta$ is one
likelihood ratio, not pointwise one. Under $P_\theta$ the process is a nonnegative martingale and $E_{P_\theta}E_n^\theta=1$:
each new independent factor has mean $\theta(q/\theta)+(1-\theta)((1-q)/(1-\theta))=1$.
Ville's inequality gives

$$P_\theta(\exists n:\ E_n^\theta\ge1/\alpha)\le\alpha.$$

Thus $\tau_\theta=\inf\{n:E_n^\theta\ge1/\alpha\}$, with value $\infty$ if the set is empty, has false-alarm probability at most
$\alpha$. This is a family of tests indexed by the specified null parameter, not one test uniform over an unknown defect rate.
For a production application, independent defects with a constant rate and a classification rule fixed in advance are modelling
assumptions, not conclusions about observed production data.

## Depends on

## Proof depends on

- [Doob's maximal inequality for nonnegative submartingales](../../martingales/doob-s-lp-maximal-inequality/maximal-ineq.md)

## Expansion

Ville's bound follows from the linked maximal inequality: $E^\theta$ is a nonnegative martingale with mean one under
$P_\theta$, so for each $n$, $P_\theta(\max_{k\le n}E_k^\theta\ge1/\alpha)\le\alpha\,E_{P_\theta}E_n^\theta=\alpha$, and these events
increase to $\{\exists n:\ E_n^\theta\ge1/\alpha\}$, so continuity from below gives the displayed bound. Link the existing result
for the Bernoulli likelihood-ratio process (nonnegative supermartingale with initial mean one) once its page exists.
Construct the product-law family and prove its coordinate marginals and independence; keep the zero extension outside
binary values when matching the existing process. Do not create a second generic likelihood-ratio or Ville theorem.

## Sources

- A. Ramdas, P. Grünwald, V. Vovk and G. Shafer, Game-theoretic statistics and safe anytime-valid inference, *Statistical Science* 38 (2023), Section 2.5, Ville's inequality, Equation (8), <https://arxiv.org/abs/2210.01948>.
