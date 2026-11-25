# Chain paths of the stochastic SEIR model with vital dynamics

Let `β`, `σ`, `γ`, `μ` be real, `N ∈ ℕ`, and for each [channel](channel.md) `c` let
`y_c : [0, ∞) → ℕ` be a function (in the intended reading, the path of a driving unit-rate counting
process). Count paths `S, E, I, R : ℝ → ℕ` form a chain path at population scale `N` driven by the
`y_c` (Kurtz's random time-change representation; Ethier–Kurtz 1986, ch. 6, (4.1) and ch. 11, (2.1))
if they are measurable and, for every `t ≥ 0`, writing `Y_c = y_c(A_c(t))` with `A_c` the
[internal clock](clock.md) of `c` along `(S, E, I, R)`,

`S(t) = S(0) + Y_birth - Y_infection - Y_deathS`,

`E(t) = E(0) + Y_infection - Y_progression - Y_deathE`,

`I(t) = I(0) + Y_progression - Y_recovery - Y_deathI`,

`R(t) = R(0) + Y_recovery - Y_deathR`,

as real numbers. The equations say nothing about negative times.

When `β, σ, γ, μ ≥ 0`, `N ≥ 1` and the `y_c` are independent unit-rate Poisson processes, these are
the random time-change equations of the continuous-time Markov chain on `ℕ⁴` with births `S → S + 1`
at rate `μ N`, infections `(S, E) → (S - 1, E + 1)` at rate `β S I / N`, progressions
`(E, I) → (E - 1, I + 1)` at rate `σ E`, recoveries `(I, R) → (I - 1, R + 1)` at rate `γ I`, and
deaths `X → X - 1` at rate `μ X` for each compartment `X`; each rate vanishes where its jump would
make a count negative. The counts are natural numbers, so they are nonnegative by construction;
measurability of the paths (a càdlàg path is measurable) makes the intensities along them measurable
functions of time. The population is not conserved, and `N` is the scale of the birth rate `μ N` and
of the incidence `β S I / N`, not the size of the initial population.
