# One sample path of the stochastic SEIR chain with vital dynamics

**One sample path of the stochastic SEIR chain with vital dynamics** at population scale `N`
(Kurtz's random time-change representation; Ethier–Kurtz 1986, ch. 6, (4.1) and ch. 11, (2.1)).
Given the paths `y c` of the eight driving unit-rate counting processes, the counts
`S, E, I, R : ℝ → ℕ` satisfy, for `t ≥ 0`, writing `Y_c = y c (clock c t)`,

`S(t) = S(0) + Y_birth - Y_infection - Y_deathS`,
  `E(t) = E(0) + Y_infection - Y_progression - Y_deathE`,
  `I(t) = I(0) + Y_progression - Y_recovery - Y_deathI`,
  `R(t) = R(0) + Y_recovery - Y_deathR`.

When the `y c` are independent unit-rate Poisson processes this is the continuous-time Markov
chain with the jumps and rates of the module docstring. The counts are natural numbers, so they
are nonnegative by construction; the paths are required to be measurable (a càdlàg path is), so
that the clocks are genuine Lebesgue integrals. The population is not conserved, and `N` is the
scale of the birth rate `μ N` and of the incidence `β S I / N`, not the size of the initial
population.
