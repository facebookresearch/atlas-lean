# Regeneration of stochastic reaction networks

## Stopping times, shifts and the strong Markov property of i.i.d. steps

- [Stopping time of the step sequence](is-step-stopping-time.md)
- [Set of step sequences determined before a random time](is-determined-before.md)
- [Steps after a random time](shift-at.md)
- [The σ-algebra of the first $n$ steps](past-sigma.md)
- [The σ-algebra of the steps from index $n$ on](future-sigma.md)
- [The first $n$ steps generate every measurable set they determine](measurable-set-past-sigma.md)
- [The shift of the step sequence by $n$ steps is measurable](measurable-ctmc-shift-pi.md)
- [Shifting to a measurable random time is measurable](measurable-shift-at.md)
- [Strong Markov property of an i.i.d. step sequence](measure-inter-shift-at-preimage.md)
- [Strong Markov property at an almost surely finite stopping time](map-prod-shift-at.md)

## Visits, rewards and regeneration cycles along the jump chain

- [The jump chain up to step $n$ depends only on the first $n$ steps](ctmc-jump-chain-congr.md)
- [Number of visits to a state before step $n$](n-visits.md)
- [A visit makes the visit counts at all later steps strictly larger](n-visits-lt-of-lt.md)
- [At most one visit has exactly $k$ earlier visits](eq-of-visit.md)
- [The $k$-th visit to a state, counting from zero](visit.md)
- [Visit times are stopping times of the step sequence](is-step-stopping-time-visit.md)
- [More than $k$ visits before step $n$ put the $k$-th visit before $n$](exists-visit-lt-of-lt-n-visits.md)
- [If the $k$-th visit is at step $n$, every earlier visit is by step $n$](visit-le-of-visit-eq.md)
- [The first visit is finite exactly when the chain ever visits the state](visit-zero-ne-top-iff.md)
- [From $x_0$, the first return is finite exactly when $x_0$ is revisited](visit-self-one-ne-top-iff.md)
- [Between step 0 and a finite first return, the chain avoids $x_0$](ctmc-jump-chain-ne-of-lt-visit-one.md)
- [Visit counts split at a visit into earlier and restarted counts](n-visits-add.md)
- [Visits after a visit](visit-add.md)
- [Reward of an observable over the first $m$ holding times](reward.md)
- [Rewards split at any step into earlier and restarted rewards](reward-add.md)
- [Rewards up to step $m \le n$ depend only on the first $n$ steps](reward-congr.md)
- [Reward collected until the first return to the starting state](return-reward.md)
- [Reward collected during the $k$-th regeneration cycle](cycle-sum.md)
- [A completed cycle's reward is the return reward of the shifted steps](cycle-sum-eq.md)
- [Cycle sums depend only on the steps before a finite later visit](cycle-sum-congr.md)
- [For countable $S$, sets determined by $Y_0, \dots, Y_n$ are measurable](measurable-set-of-jump-chain.md)

## The Abel functional and the resolvent identity

- [Abel functional of the jump–hold chain](abel-sum.md)
- [First-step decomposition of the Abel functional](abel-sum-eq.md)
- [For $q > 0$, $E_k \ge 0$, $g \le 1$, the Abel functional is at most 1](abel-sum-le-one.md)
- [A rate-one exponential clock is almost surely nonnegative](ae-nonneg-exp-measure-one.md)
- [First-step equation of the mean Abel functional for $q > 0$, $a \ge 0$](lintegral-abel-sum.md)
- [Resolvent identity for weights balancing the rate-weighted jump kernel](tsum-mul-lintegral-abel-sum.md)

## The path: occupation integrals and Laplace transforms

- [Before time 0 the path is at its initial state](path-of-neg.md)
- [Occupation integral up to the $m$-th jump time equals the reward](integral-path-jump-time.md)
- [Occupation integrals of bounded observables are Lipschitz in time](abs-integral-path-sub-le.md)
- [The Abel functional is the Laplace transform of a non-explosive path](lintegral-exp-path-eq-abel-sum.md)
- [Real value of the Abel functional of a non-explosive path](abel-sum-to-real-eq.md)

## An Abelian theorem for functions with values between 0 and 1

- [For $a > 0$, $\int_t^\infty a^2 e^{-a r}\,dr = a e^{-a t}$](lintegral-ici-sq-mul-exp.md)
- [Abelian theorem: Cesàro limits of $0 \le h \le 1$ are Abel limits](tendsto-abel-of-tendsto-cesaro.md)

## Identification of almost sure time-average limits

- [A common almost sure limit of time averages is the balanced-law mean](eq-tsum-of-ae-tendsto.md)

## Hitting probabilities, visits and recurrence

- [First-step analysis: averaging over the first jump target](lintegral-comp-first.md)
- [Probability that the jump chain ever visits a given state](hit-prob.md)
- [Hitting probabilities satisfy the first-step equation off the target](hit-prob-eq.md)
- [Return probability to $x_0$ as an average of hitting probabilities](measure-return-eq.md)
- [Probabilities of successive visits multiply by the return probability](measure-visit-succ.md)
- [A return probability below 1 gives finitely many visits almost surely](ae-exists-visit-eq-top.md)
- [Non-explosive path, finitely many visits: zero time fraction at $x_0$](tendsto-integral-indicator-div-zero.md)
- [Without explosion, states charged by a balanced law are recurrent](measure-return-eq-one.md)
- [A recurrent state is hit almost surely from every state it reaches](hit-prob-eq-one.md)
- [A recurrent state reaching all states is visited infinitely often a.s.](ae-forall-visit-ne-top.md)

## Regeneration cycles, positive recurrence and the ergodic theorem

- [Almost surely every clock of the step sequence is positive](ae-clock-pos.md)
- [After an almost surely finite visit, later steps have the input law](map-shift-at-visit.md)
- [If all visits are almost sure, cycle rewards have the excursion law](ident-distrib-cycle-sum.md)
- [If all visits are almost sure, distinct cycle rewards are independent](indep-fun-cycle-sum-of-lt.md)
- [On a return to $x_0$, the excursion spends one holding time at $x_0$](return-reward-indicator-eq.md)
- [With every visit, positive rates and clocks make visit times increase](strict-mono-jump-time-visit.md)
- [Rewards up to successive visits telescope into the cycle rewards](reward-visit-eq.md)
- [Renewal–reward when all visits to a positive recurrent state happen](ae-tendsto-of-integrable.md)
- [Balanced law charging $x_0$ and no explosion give positive recurrence](integrable-return-reward.md)
- [Balanced law charging $x_0$ and reachability from it give ergodicity](ergodic-of-balanced.md)

## Stochastic mass-action networks, complex balance and ergodicity

- [Stochastic mass-action network with nonnegative rate constants](mass-action.md)
- [Rate-weighted jump kernel of a stochastic reaction network](of-real-hold-rate-mul-jump-pmf.md)
- [Inflow along one reaction comes from its unique predecessor](tsum-ite-fire-eq.md)
- [Complex balance makes the Poisson weights balance the jump kernel](tsum-poisson-weight-mul-hold-rate-mul-ju.md)
- [Reactions of positive propensity give jumps of positive probability](refl-trans-gen-jump-pmf.md)
- [Jump times tending to infinity bound molecule counts up to each time](no-explosion-path.md)
- [Complex balance and a drift bound give stationarity in Laplace form](tsum-poisson-weight-mul-lintegral-laplac.md)
- [Positive complex balance, drift bound and reachability give ergodicity](ergodic-of-is-complex-balanced-of-reacha.md)
- [Complex-balanced Poisson start, drift bound, reachability: ergodicity](ergodic-of-is-complex-balanced-of-reacha-2.md)

## Related topics

- [Complex balancing and the deficiency-zero theorem](../../../Biology/systems-biology/complex-balancing-and-the-deficiency-zero-theore/README.md): the deterministic theory of complex balancing: complex-balanced states are equilibria of the mass-action system, and a weakly reversible network of deficiency zero with finitely many species and reactions has a complex-balanced state with positive coordinates for every choice of positive rate constants, so the complex-balance hypothesis of the product-form results holds for it (the stationarity and ergodic results also need a drift bound, and the ergodic results reachability).
