# Stochastic SEIR epidemic with vital dynamics

The stochastic SEIR epidemic with births and deaths at population scale `N`: natural-number counts
`(S, E, I, R)` that change by births into `S`, infections `S → E`, progressions `E → I`, recoveries
`I → R` and deaths from each compartment, given by Kurtz's random time-change equations. The pages
relate the chain to the stochastic mass-action system of a reaction network and compare the scaled
counts with the SEIR system with vital dynamics at scale `1`.

## Channels and intensities

- [Reaction channels of the SEIR chain](channel.md)
- [Scaled intensities of the eight channels](scaled-rate.md)
- [Common bound for the scaled intensities](rate-bound.md)
- [The scaled intensities are bounded on a box](scaled-rate-le.md)
- [Lipschitz bound for the scaled intensities](abs-scaled-rate-sub-le.md)

## Chain paths, clocks and deviation

- [Intensities of the channels along count paths](rate.md)
- [Internal clocks of the channels](clock.md)
- [Internal clocks in scaled form](clock-eq.md)
- [The birth clock does not depend on the state](clock-birth.md)
- [Chain paths of the stochastic SEIR model with vital dynamics](is-chain-path.md)
- [Deviation of the scaled chain from a deterministic path](deviation.md)

## The reaction network

- [Compartments of the SEIR model](compartment.md)
- [Vectors indexed by the four compartments](vec4.md)
- [Reactant complexes of the SEIR network](network-src.md)
- [Product complexes of the SEIR network](network-prod.md)
- [The SEIR reaction network with vital dynamics](network.md)
- [Rate constants of the SEIR network](rate-const.md)
- [Stochastic mass-action system of the SEIR network](chain-crn.md)
- [Mass-action rates of the SEIR network are the scaled intensities](network-rate-eq.md)
- [Mass-action propensities equal the chain's intensities](propensity-chain-crn.md)
- [Total ℓ¹ norm of the SEIR reaction vectors is 11](stoich-norm-network.md)

## Bridge to the mass-action system

- [Count vector path frozen at negative times](to-path.md)
- [Deterministic path as a vector over the compartments](ode-path.md)
- [At nonnegative times the two forms of the deviation agree](deviation-to-path.md)
- [SEIR solutions solve the mass-action system of the network](has-deriv-at-ode-path.md)
- [At nonnegative times the two forms of the internal clocks agree](clock-to-path.md)
- [The population grows only by births](total-le.md)
- [SEIR chain paths are chain paths of the mass-action system](to-crn.md)

## Kurtz's estimate and law of large numbers

- [Kurtz's pathwise estimate for SEIR with vital dynamics](deviation-le.md)
- [Kurtz's law of large numbers for SEIR with vital dynamics](tendsto-measure-deviation.md)
- [Kurtz's theorem for SEIR with vital dynamics, supremum form](tendsto-measure-i-sup-deviation.md)
- [Deterministic initial counts with convergent scaled values satisfy Kurtz's initial condition](tendsto-measure-deviation-zero-of-initia.md)
- [If R₀ > 1 and scaled initial counts tend to positive S, E, I, the chain nears the endemic state](eventually-tendsto-measure-endemic.md)
