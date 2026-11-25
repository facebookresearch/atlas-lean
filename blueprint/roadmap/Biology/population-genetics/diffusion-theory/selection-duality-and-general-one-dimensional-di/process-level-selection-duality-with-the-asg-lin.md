# Selection duality for every solution of the Wright–Fisher martingale problem

Let $\sigma\ge0$, $x\in[0,1]$, and let $X$ be any [solution of the Wright–Fisher martingale problem](../fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md) under a probability measure $\mu$, with $X_0=x$ almost surely. Let $N$ be the [specific non-explosive ASG line count](realized-asg-line-counting-process-countable-ctm.md), started at $n\in\mathbb N_0$. Then

$$\mathbb E_\mu[(1-X_t)^n]=\mathbb E_n[(1-x)^{N_t}]\qquad(t\ge0).$$

The expectations may be on different probability spaces; no pathwise coupling of $X$ and $N$ is asserted. At $n=0$, both sides are one, using the usual convention for zeroth powers and the absorbing zero-line extension. No Markov property or uniqueness assumption for $X$ is needed.

## Moment equation

Put $h_n(y)=(1-y)^n$ and $u_n(t)=\mathbb E_\mu[h_n(X_t)]$. These functions satisfy $0\le u_n(t)\le1$. The [fixed-time Dynkin formula](../fixation-and-absorption-in-the-wright-fisher-dif/integral-generator.md) and the [operator duality](generator-one-sub-pow-eq-asg-generator.md) give

$$u_n(t)=(1-x)^n+\int_0^t(A_\sigma u(s))(n)\,ds.$$

For each fixed $n$, all polynomial test functions and generator terms are bounded on $[0,1]$. Continuous sample paths and bounded convergence make their expectations continuous in time, justify Fubini, and show that $u_n$ is continuously differentiable with $u'_n=(A_\sigma u)(n)$. This uses the generator identity without assuming the process duality.

## Bounded stopped-duality argument

Fix $T\ge0$, $n\ge1$ and an integer $M>n$. Let $\tau_M$ be the first time $N$ reaches $M$. On the finite stopped chain consider the time-dependent function $(s,j)\mapsto u_j(T-s)$. Before stopping, its time derivative plus its chain-generator drift is

$$-u'_j(T-s)+(A_\sigma u(T-s))(j)=0.$$

Finite-state time-dependent Dynkin, stopped at $T\wedge\tau_M$, therefore gives

$$u_n(T)=\mathbb E_n\!\left[u_{N_{T\wedge\tau_M}}(T-T\wedge\tau_M)\right].$$

On $\{\tau_M>T\}$ the integrand is $u_{N_T}(0)=(1-x)^{N_T}$. On the remaining event both this integrand and $(1-x)^{N_T}$ lie in $[0,1]$. The explicit [escape estimate](realized-asg-line-counting-process-countable-ctm.md) thus gives

$$\left|u_n(T)-\mathbb E_n[(1-x)^{N_T}]\right|\le\mathbb P_n(\tau_M\le T)\le\frac{n e^{\sigma T}}M\longrightarrow0.$$

This proves the duality for every martingale-problem solution. It uses bounded finite-state localization rather than an unproved uniqueness assertion for an infinite ODE system or a Laplace-transform appeal. In particular, the powers of $1-X_t$ agree in expectation for all such solutions. Polynomials are dense in the continuous functions on $[0,1]$, so their one-time probability laws agree. This last observation alone is not a claim about equality of entire path laws.

## Long-time consequence

For each $n\ge1$, the [positive-class convergence of the line count](asg-line-count-positive-recurrence-and-convergen.md) and the bounded function $k\mapsto(1-x)^k$ imply, when $\sigma>0$,

$$\lim_{t\to\infty}\mathbb E_\mu[(1-X_t)^n]=\sum_{k\ge1}\pi_k^\sigma(1-x)^k=1-u_\sigma(x).$$

The last equality is the [stationary generating-function identity](has-sum-asg-stationary-mul-one-sub-pow.md). For $\sigma=0$, the line count reaches one and the limit is $1-x$. This conclusion excludes $n=0$, whose moment remains one. Its interpretation as loss or fixation additionally uses absorption, as in [fixation from the ASG](fixation-probability-from-the-asg.md).

## Depends on

- [Martingale problem for the Wright–Fisher diffusion](../fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md)
- [The ancestral selection graph line count as a non-explosive chain](realized-asg-line-counting-process-countable-ctm.md)

## Proof depends on

- [Dynkin's formula at a fixed time](../fixation-and-absorption-in-the-wright-fisher-dif/integral-generator.md)
- [Selection duality in operator form](generator-one-sub-pow-eq-asg-generator.md)
- [The ancestral selection graph line count as a non-explosive chain](realized-asg-line-counting-process-countable-ctm.md)
- [Positive recurrence and convergence of the ancestral selection graph line count](asg-line-count-positive-recurrence-and-convergen.md)
- [Loss probability from the stationary ancestral selection graph](has-sum-asg-stationary-mul-one-sub-pow.md)

## Related

- [Fixation probability from the ancestral selection graph](fixation-probability-from-the-asg.md)

## Scope

The proof uses the realized chain and Dynkin's formula for it at bounded stopping times. The operator identity is the linked statement. The ASG duality and its sampling interpretation are also described by the related ASG page; this page adds the process-level form.

## Sources

- M. Birkner, *Stochastic population models*, 2025/26, <https://www.staff.uni-mainz.de/birkner/SPM2526/StochPopModels_25-26.pdf>, Section 3.4.1, Observation 3.4.6 and equation (3.14), and Remark 2.1.3. Both mutation parameters are zero and the source convention is $\sigma_B=2\sigma$. The stopped argument above makes the passage from generator identity to bounded process duality explicit.
