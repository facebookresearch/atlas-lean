# Fixation probability via the ancestral selection graph line count

Let $\sigma>0$, $x\in[0,1]$, and let $X$ be any [solution of the Wright–Fisher martingale problem](../fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md) under a probability measure, with $X_0=x$ almost surely. Use the [same realized ASG line count](realized-asg-line-counting-process-countable-ctm.md) as in the process-level duality. Then the probability of eventual fixation of the favored allele is

$$\mathbb P_x(X\text{ is eventually absorbed at }1)=1-\sum_{k\ge1}\pi_k^\sigma(1-x)^k=\frac{1-e^{-2\sigma x}}{1-e^{-2\sigma}}.$$

This is a genealogical derivation of the [process fixation formula](../fixation-and-absorption-in-the-wright-fisher-dif/measure-real-fixation.md), not a new closed form for fixation.

## The process-level limit

The [finite absorption theorem](../fixation-and-absorption-in-the-wright-fisher-dif/ae-exists-absorbed.md) says that almost every path is eventually constantly zero or eventually constantly one. These two events partition the probability space up to a null set. Thus

$$1-X_t\longrightarrow\mathbf1_{\{X\text{ eventually absorbed at }0\}}\quad\text{almost surely},$$

and bounded convergence identifies the limit of $\mathbb E[1-X_t]$ with the loss probability. The [duality](process-level-selection-duality-with-the-asg-lin.md), used at $n=1$, gives

$$\mathbb E[1-X_t]=\mathbb E_1[(1-x)^{N_t}].$$

The law on the right is exactly that of the chain constructed in the line-count page. If another standard conservative Markov jump realization is used, its identification in law follows from the unique non-explosive minimal law with these rates and the same initial state; equality of an abstract generator formula alone is not the law-identification step.

By [positive-class convergence](asg-line-count-positive-recurrence-and-convergen.md), $N_t$ started at one tends in total variation to the [positive stationary law](asg-stationary.md). Since $0\le(1-x)^k\le1$, this gives

$$\mathbb P_x(\text{loss})=\lim_{t\to\infty}\mathbb E_1[(1-x)^{N_t}]=\sum_{k\ge1}\pi_k^\sigma(1-x)^k.$$

The [stationary generating-function identity](has-sum-asg-stationary-mul-one-sub-pow.md) evaluates the sum as $1-u_\sigma(x)$, with $u_\sigma$ given by [Kimura's formula](../wright-fisher-diffusion/kimura-fixation.md). Taking the complement yields the stated fixation probability. The argument connects absorption, the stationary series and the fixation formula through the realized ASG.

## Boundary and scaling checks

At $x=0$ fixation has probability zero; at $x=1$ it has probability one. At $\sigma=0$, the ASG line count started at one stays at one, so the same bounded-limit argument gives loss probability $1-x$ and fixation probability $x$.

The small-selection limit also follows from the stationary laws rather than an undefined substitution into a zero denominator. For $\sigma>0$,

$$|u_\sigma(x)-x|\le d_{\mathrm{TV}}(\pi^\sigma,\delta_1)=1-\frac{2\sigma}{e^{2\sigma}-1}\longrightarrow0,$$

uniformly for $x\in[0,1]$. The diffusion convention is $L_\sigma f=\tfrac12x(1-x)f''+\sigma x(1-x)f'$ and ASG branching is $\sigma$ per line. Birkner's selection parameter therefore satisfies $\sigma_B=2\sigma$; this bridge is what produces the factor $2\sigma$ in both the stationary Poisson parameter and Kimura's exponential formula. Mutation is absent throughout.

## Depends on

- [Martingale problem for the Wright–Fisher diffusion](../fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md)
- [Stationary law of the ancestral selection graph line counts](asg-stationary.md)
- [The ancestral selection graph line count as a non-explosive chain](realized-asg-line-counting-process-countable-ctm.md)

## Proof depends on

- [Selection duality for every solution of the Wright–Fisher martingale problem](process-level-selection-duality-with-the-asg-lin.md)
- [Positive recurrence and convergence of the ancestral selection graph line count](asg-line-count-positive-recurrence-and-convergen.md)
- [Absorption in finite time](../fixation-and-absorption-in-the-wright-fisher-dif/ae-exists-absorbed.md)
- [Loss probability from the stationary ancestral selection graph](has-sum-asg-stationary-mul-one-sub-pow.md)

## Related

- [Kimura's fixation probability, process form](../fixation-and-absorption-in-the-wright-fisher-dif/measure-real-fixation.md)

## Scope

A proof page must still supply the process-level duality with the ancestral selection graph and the convergence theorem for countable-state chains. The fixation formula itself does not establish this genealogical route, and no construction of the full labeled ancestral graph is claimed.

## Sources

- M. Birkner, *Stochastic population models*, 2025/26, <https://www.staff.uni-mainz.de/birkner/SPM2526/StochPopModels_25-26.pdf>, Section 3.4.1 and equation (3.14), with both mutation parameters zero and $\sigma_B=2\sigma$. The limit argument is given above using the linked absorption and stationary generating-function results.
