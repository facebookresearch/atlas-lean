# Non-explosion of stochastic reaction networks

## Steps, clocks, holding times and jump times of the jump–hold chain

- [Law of one step of the jump–hold chain](step-measure.md)
- [Law of the i.i.d. step sequence driving the jump–hold chain](input-measure.md)
- [Joint law of the first step and the shifted step sequence](input-measure-map-first.md)
- [The clock of one step has the rate-one exponential law](step-measure-map-snd.md)
- [Each clock of the step sequence has the rate-one exponential law](input-measure-map-clock.md)
- [Laplace transform of the rate-one exponential law at $a \ge 0$](lintegral-exp-neg-mul-exp-measure-one.md)
- [Almost surely every clock of the step sequence is nonnegative](ae-clock-nonneg.md)
- [Almost surely the partial sums of the clocks tend to infinity](ae-tendsto-sum-clock.md)
- [Holding times of the jump–hold chain](holding-time.md)
- [Jump times of the jump–hold chain](jump-time.md)
- [First-step decomposition of the jump chain](ctmc-jump-chain-succ-eq.md)
- [First-step decomposition of the jump times](jump-time-succ-eq.md)
- [Positive rates and nonnegative clocks give nonnegative jump times](jump-time-nonneg.md)

## Stopped discounted process, drift bounds and non-explosion

- [Stopped discounted process of the jump–hold chain](discounted-stop.md)
- [Before entering $A$, the stopped process equals $e^{-cT_n} V(Y_n)$](discounted-stop-eq-of-forall-not-mem.md)
- [The stopped discounted process freezes at the first entrance into $A$](discounted-stop-eq-of-hit.md)
- [On a countable space the stopped discounted process is measurable](measurable-discounted-stop.md)
- [A drift condition off $A$ bounds the stopped process's mean by $V(x)$](lintegral-discounted-stop-le.md)
- [Under a drift condition, a discounted moment bound for the jump chain](lintegral-exp-jump-time-mul-le.md)
- [Under a drift condition, a bound on reaching $\{V \ge m\}$ by time $t$](measure-reach-le.md)
- [Non-explosion of the jump–hold chain under a Foster–Lyapunov condition](ae-tendsto-jump-time-at-top.md)

## Path of the jump–hold chain and its fixed-time moment bound

- [State at time $s$ of the jump–hold chain stopped after $n$ jumps](state-at.md)
- [For $0 \le s < T_m$, later jumps do not change the state at time $s$](state-at-eq-of-lt.md)
- [For $k < n$, the stopped chain is at $Y_k$ between $T_k$ and $T_{k+1}$](state-at-eq-ctmc-jump-chain.md)
- [Path of the jump–hold chain](path.md)
- [For $0 \le s < T_n$, the path at time $s$ is the state after $n$ jumps](state-at-eq-path.md)
- [Between the jump times $T_k$ and $T_{k+1}$ the path is at $Y_k$](path-eq-ctmc-jump-chain.md)
- [On a countable space the state at time $s$ is jointly measurable](measurable-state-at.md)
- [Drift-condition moment bound at time $s \ge 0$ after at most $n$ jumps](lintegral-state-at-le.md)
- [Moment bound at a time $t \ge 0$ under a Foster–Lyapunov condition](lintegral-path-le.md)

## Stochastic reaction networks and their jump–hold chain

- [Stochastic chemical reaction network](stochastic-crn.md)
- [Total propensity of a stochastic reaction network](total-rate.md)
- [Holding rate, with a fictitious rate one at absorbing states](hold-rate.md)
- [Generator of a stochastic reaction network](generator.md)
- [Law of the next reaction at a state with nonzero total propensity](reaction-pmf.md)
- [Jump kernel of a stochastic reaction network](jump-pmf.md)
- [Law of the steps driving a stochastic reaction network](input-measure-2.md)
- [Jump times of a stochastic reaction network](jump-time-2.md)

## Drift bounds and non-explosion of stochastic reaction networks

- [Adding a constant does not change the generator](generator-add-const.md)
- [Propensity-weighted sum of the values after one reaction](sum-propensity-mul-jump.md)
- [A generator bound at a state gives the one-step drift condition](drift-of-generator-le.md)
- [Bounded total propensity on sublevel sets bounds the holding rates](hold-rate-bdd.md)
- [Discounted Lyapunov moment bound for a stochastic reaction network](lintegral-exp-jump-time-mul-le-2.md)
- [Drift criterion for non-explosion of a stochastic reaction network](ae-tendsto-jump-time-at-top-2.md)
- [Total propensity is bounded on sublevel sets of a coercive function](bdd-rate-of-coercive.md)
- [Non-explosion with a coercive Lyapunov function](ae-tendsto-jump-time-at-top-of-coercive.md)
- [Under the drift criterion, the jump times are almost surely unbounded](ae-forall-exists-lt-jump-time.md)

## Path and fixed-time moment bound of a stochastic reaction network

- [Path of a stochastic reaction network](path-2.md)
- [Fixed-time Lyapunov moment bound for a stochastic reaction network](lintegral-path-le-2.md)

## Related topics

- [Complex balancing and the deficiency-zero theorem](../../../Biology/systems-biology/complex-balancing-and-the-deficiency-zero-theore/README.md): complex balancing and the deficiency-zero theorem for the deterministic mass-action system of the same networks.
