# One sample path of a stochastic reaction network

**One sample path of a stochastic reaction network** in Kurtz's random time-change
representation (Ethier–Kurtz 1986, ch. 6, (4.1); Anderson–Kurtz 2015): given paths `y r`
of the driving unit-rate counting processes, one per reaction, the counts satisfy, for `t ≥ 0`,

`X(t) = X(0) + ∑_r y_r(∫₀ᵗ λ_r(X(s)) ds) (prod r - src r)`.

When the `y r` are independent unit-rate Poisson processes, this is the Markov chain in which
reaction `r` fires at rate `λ_r(X)`. The coordinates are required to be measurable (a càdlàg path
is) and the propensities locally integrable along the path (they are locally bounded along a
non-explosive path), so that the clocks are genuine Lebesgue integrals.
