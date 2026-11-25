# Stochastic SIR epidemic and its law of large numbers

## Sequences, product laws and partial integrals

- [Tail of a sequence](seq-tail.md)
- [Joint law of the head and the tail of an i.i.d. sequence](infinite-pi-map-head-tail.md)
- [Tonelli formula over an i.i.d. sequence, split into head and tail](lintegral-infinite-pi-head-tail.md)
- [Resampling one coordinate preserves a product of probability laws](pi-map-update.md)
- [Tonelli formula over a product law with one coordinate resampled](lintegral-pi-update.md)
- [Partial integrals of jointly measurable functions against an s-finite measure are measurable](measurable-lintegral-of-uncurry.md)

## Competing exponential clocks and their null sets

- [Density of the rate-one exponential law](exp-dens.md)
- [Competing exponential clocks, joint law](lintegral-competing.md)
- [A rate-one exponential clock is nonpositive with probability zero](exp-measure-iic-zero.md)
- [Ties of two independent rate-one exponential clocks are null when one speed is positive](prod-exp-measure-tie.md)
- [For $b \ge 0$ and a rate-one exponential clock $r_1$, the event $b r_1 < 0$ has probability zero](prod-exp-measure-neg.md)
- [For $a \ge 0$ and a rate-one exponential clock $r_2$, the event $a r_2 < 0$ has probability zero](prod-exp-measure-neg-2.md)

## Two-channel chains driven by unit clocks

- [Clock configuration of a two-channel chain](clock-config.md)
- [Law of a clock configuration with independent exponential clocks](clock-measure.md)
- [Two-channel chain](two-channel.md)
- [Valid two-channel chain](is-valid.md)
- [Total rate of a two-channel chain](total-rate.md)
- [Holding time read off the residual clocks of a two-channel chain](hold.md)
- [State after the next jump of a two-channel chain](next.md)
- [Clock configuration after the next jump](next-clock.md)
- [One jump of a two-channel chain with its clocks](step.md)
- [State and clocks after $n$ steps of a two-channel chain](config.md)
- [Rate matrix of a two-channel chain](rate-matrix.md)
- [Markov chain step read off one jump of the clock chain](output.md)
- [Steps read off the clock chain](steps.md)
- [The path of the clock chain](path.md)

## One jump of exponential clocks

- [Jump matrix of a valid two-channel chain at an active state](ctmc-jump-matrix-eq.md)
- [Integrals against a row of the jump matrix at an active state](lintegral-ctmc-jump-pmf.md)
- [Iterated integrals of a measurable function against the clock-configuration law](lintegral-clock-measure.md)
- [One jump of the clocks from an active state](map-clock.md)

## Jump chain, holding times and law of the clock chain

- [Paths with the same jump chain and jump times agree](ctmc-path-congr.md)
- [The steps after the first are those of the restarted chain](steps-succ.md)
- [The read-off steps have the clock chain's states as jump chain](ctmc-jump-chain-steps.md)
- [Holding times of the steps read off the clock chain](ctmc-holding-time-steps.md)
- [The path does not depend on the auxiliary steps](ctmc-path-steps.md)
- [First step and restarted input of the clock chain](first-step.md)
- [Independent Exp(1) clocks and step-law auxiliary steps give a first step with the step law](map-first-step.md)
- [Independent Exp(1) clocks and i.i.d. step-law auxiliary steps give i.i.d. step-law read-off steps](map-steps.md)
- [Under independent rate-one exponential clocks the path has the law of the Markov chain](map-path.md)
- [Finite-dimensional distributions of the clock chain](clock-measure-real-path-fdd.md)
- [Transition probabilities of the clock chain](clock-measure-real-path-eq.md)

## Event times and integrated rates along a path

- [Duration of a jump of the clock chain](dur.md)
- [Real event times of the clock chain](event-time.md)
- [Jump times as event times before absorption, for nonnegative durations](ctmc-jump-time-steps-eq.md)
- [After a state of total rate zero the next jump time is infinite](ctmc-jump-time-steps-succ-eq-top.md)
- [Between consecutive jump times the path is the current state](path-eq-config.md)
- [The path of the clock chain on the real line](real-path.md)
- [Real path of a chain absorbed after $n$ jumps, between event times](real-path-eq.md)
- [For $u \le t$, integral of a function equal to $C$ for $u \le s < t$](integral-eq-of-forall-ico.md)
- [Integral of a function of the state along the real path](integral-real-path.md)
- [Three cases of a jump from an active state with positive residuals](jump-cases.md)
- [Holding-time bounds from an active state with positive residuals](hold-bounds.md)
- [Internal clock of channel 1 after $n$ jumps](internal.md)
- [Internal clock of channel 2 after $n$ jumps](internal-2.md)

## SIR states, clocks and paths

- [State space of the SIR chain in a population of size $N$](sirstate.md)
- [The SIR epidemic as a two-channel chain](sir-channels.md)
- [Initial clock configuration of two unit clocks](init-clock.md)
- [Counting path of a unit clock](clock-count.md)
- [The SIR path driven by two unit clocks](sir-path.md)
- [Susceptible count of the SIR path](sir-s.md)
- [Infective count of the SIR path](sir-i.md)
- [Removed count of the SIR path](sir-r.md)
- [Arrival times of a unit clock](arrival.md)
- [The clock count is $k$ between the $k$-th and the next arrival](clock-count-eq.md)

## Invariant, absorption and pathwise construction of the SIR chain

- [Bookkeeping invariant of the SIR chain after $n$ jumps](sirinv.md)
- [A jump of the SIR chain from an active state lowers $2S + I$](sir-next-potential.md)
- [The constructed SIR chain is absorbed after at most $2N$ jumps](sir-exists-absorbing.md)
- [Jumps of the constructed SIR chain take nonnegative time](sir-dur-nonneg.md)
- [The SIR path solves the time-change equations at each time $t \ge 0$](sir-time-change.md)
- [Pathwise existence of the SIR chain](is-chain-path-sir.md)
- [The SIR path starts at its initial state](sir-path-zero.md)

## Independent exponential clocks and the law of the SIR path

- [Law of the interarrival times of two independent unit clocks](clock-law.md)
- [Composing with a measure-preserving map preserves independence](i-indep-fun-comp-of-map-eq.md)
- [Rate-one exponential interarrival times of two clocks are almost surely all positive](ae-clock-law-pos.md)
- [Almost-sure existence of the SIR chain](ae-is-chain-path-sir.md)
- [With i.i.d. Exp(1) interarrival times, the infection clock is a rate-one Poisson process](is-poisson-process-clock-count-fst.md)
- [With i.i.d. Exp(1) interarrival times, the recovery clock is a rate-one Poisson process](is-poisson-process-clock-count-snd.md)
- [Law of the initial clock configuration of two independent rate-one exponential clocks](clock-law-map-init-clock.md)
- [Law identification for the SIR chain](map-sir-path.md)
- [Law identification for the SIR chain on any probability space](map-sir-path-of-has-law.md)
- [Transition probabilities of the SIR chain](clock-law-real-sir-path-eq.md)

## Kurtz's law of large numbers

- [Infection clock: the integrated infection rate along a path](infection-clock.md)
- [Recovery clock: the integrated recovery rate along a path](recovery-clock.md)
- [Random time-change equations of the stochastic SIR chain](is-chain-path.md)
- [Deviation of the scaled chain from a deterministic path](deviation.md)
- [Conservation of the population along a chain path](total-eq.md)
- [The scaled counts of a chain path lie in the unit interval](scaled-mem-icc.md)
- [Kurtz's pathwise estimate for the SIR chain](deviation-le.md)
- [Chebyshev bound for a scaled unit Poisson increment](measure-le-abs-div-sub-le.md)
- [A $C/N$ bound in the uniform law of large numbers for Poisson clocks](exists-measure-poisson-clock-le.md)
- [Uniform law of large numbers for unit Poisson clocks](tendsto-measure-poisson-clock.md)
- [Kurtz's law of large numbers for the stochastic SIR epidemic](tendsto-measure-deviation.md)
- [Kurtz's law of large numbers for SIR in supremum form](tendsto-measure-i-sup-deviation.md)
- [Deterministic initial counts with convergent scaled values satisfy Kurtz's initial condition](tendsto-measure-deviation-zero-of-initia.md)
- [Bounded convergence in probability implies convergence of means](tendsto-integral-of-tendsto-measure.md)
- [The expected infected fraction converges to the ODE solution](tendsto-integral-infected.md)
