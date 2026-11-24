# Positive recurrence and convergence of the ancestral selection graph line count

Let $\sigma>0$ and restrict the [non-explosive ASG line count](realized-asg-line-counting-process-countable-ctm.md) to its closed positive class $\{1,2,\ldots\}$. Its [stationary weights](asg-stationary.md) are

$$\pi_n^\sigma=\frac{(2\sigma)^n}{n!\,(e^{2\sigma}-1)},\qquad n\ge1.$$

This is a Poisson distribution of parameter $2\sigma$ conditioned to be positive. The chain is positive recurrent, this is its unique stationary law on the positive class, and its law converges to it in normalized total variation from each finite starting state $n\ge1$. The absorbing state zero of the extended chain is excluded from this uniqueness claim.

## From balance to semigroup invariance

The [normalization](has-sum-asg-stationary.md) and [global balance identity](asg-stationary-global-balance.md) give $\sum_n\pi_n^\sigma=1$ and $\pi^\sigma Q=0$. To justify that the latter is invariance for the realized semigroup, also check summability of the exit rates. With $\lambda=2\sigma$, the Poisson factorial moments give

$$\sum_{n\ge1}\pi_n^\sigma n=\frac{\lambda e^\lambda}{e^\lambda-1},\qquad \sum_{n\ge1}\pi_n^\sigma n(n-1)=\frac{\lambda^2e^\lambda}{e^\lambda-1},$$

and hence

$$\sum_{n\ge1}\pi_n^\sigma q_n=\frac{\lambda^2e^\lambda}{e^\lambda-1}<\infty,\qquad q_n=\sigma n+\binom n2.$$

The backward equation gives $|\partial_t p_t(n,m)|\le\sum_j|Q_{nj}|\le2q_n$. Thus differentiation under the $\pi^\sigma$ sum and interchange of the two countable sums are justified by the displayed integrability bound. For each $m\ge1$,

$$\frac{d}{dt}\sum_n\pi_n^\sigma p_t(n,m)=\sum_j\left(\sum_n\pi_n^\sigma Q_{nj}\right)p_t(j,m)=0.$$

At time zero the sum is $\pi_m^\sigma$, so $\pi^\sigma P_t=\pi^\sigma$. This checks the passage from algebraic balance to a stationary process law rather than silently substituting a finite-state result.

## Irreducibility and convergence

Every upward rate is positive and every downward rate from $n\ge2$ is positive. Any two positive states are therefore connected by a finite path of positive-rate jumps. For any fixed $\delta>0$, that path can be followed within time $\delta$ and then held at its destination with positive probability. Consequently the skeleton $P_\delta$ is irreducible, and $p_\delta(n,n)\ge e^{-q_n\delta}>0$ makes it aperiodic. It has the invariant probability $\pi^\sigma$ just verified.

Apply the standard countable-state discrete-chain theorem: an irreducible chain with an invariant probability is positive recurrent and has that unique stationary law; with aperiodicity its transition laws converge to it in total variation. The corresponding continuous-time chain is positive recurrent as well. For $t=k\delta+s$, $0\le s<\delta$, contraction of total variation under the Markov kernel $P_s$ gives

$$d_{\mathrm{TV}}\bigl(P_t(n,\cdot),\pi^\sigma\bigr)\le d_{\mathrm{TV}}\bigl(P_{k\delta}(n,\cdot),\pi^\sigma\bigr)\longrightarrow0.$$

Here $d_{\mathrm{TV}}(\nu,\eta)=\sup_B|\nu(B)-\eta(B)|$. These are countable-state recurrence and convergence facts, not merely irreducibility of a finite truncation. On the extended state space containing zero, $\delta_0$ is another stationary law, so the unique-law assertion would be false there.

## Neutral boundary

At $\sigma=0$, the same line-count construction has only deaths and, from $n\ge1$, reaches one after finitely many jumps almost surely. The [defined neutral stationary law](asg-stationary.md) is $\delta_1$. For $\sigma\downarrow0$,

$$d_{\mathrm{TV}}(\pi^\sigma,\delta_1)=1-\pi_1^\sigma=1-\frac{2\sigma}{e^{2\sigma}-1}\longrightarrow0.$$

This is convergence of the stationary laws, distinct from the long-time convergence at a fixed positive selection coefficient. The zero-line extension remains at zero even in the neutral case.

## Depends on

- [The ancestral selection graph line count as a non-explosive chain](realized-asg-line-counting-process-countable-ctm.md)
- [Stationary law of the ancestral selection graph line counts](asg-stationary.md)

## Proof depends on

- [The ancestral selection graph line count as a non-explosive chain](realized-asg-line-counting-process-countable-ctm.md)
- [Global balance of the ancestral selection graph chain](asg-stationary-global-balance.md)
- [Stationary weights under selection sum to one](has-sum-asg-stationary.md)

## Scope

The stationary-weight identities are the linked statements. A proof page must still supply invariance of $\pi^\sigma$ for the realized semigroup, the recurrence and convergence theorem for countable-state chains, and the skeleton-chain argument.

## Sources

- M. Birkner, *Stochastic population models*, 2025/26, <https://www.staff.uni-mainz.de/birkner/SPM2526/StochPopModels_25-26.pdf>, Section 3.4.1, for the ASG rates and duality context. Birkner's parameter satisfies $\sigma_B=2\sigma$ here and both mutation rates are zero. The invariant-law and convergence arguments above supply the process-level steps; the Poisson-weight identities are the linked statements.
