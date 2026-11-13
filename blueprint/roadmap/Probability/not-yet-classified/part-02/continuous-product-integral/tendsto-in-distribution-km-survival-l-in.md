# Continuous-time Kaplan–Meier limit law in `ℓ^∞((0, τ))`, conditional on Borel measurability

**Continuous-time Kaplan–Meier limit law in `ℓ^∞([0, τ])`, conditional on Borel
measurability** (van der Vaart 1998, §20.3; Gill–Johansen 1990).

Setting: `Dn n ω` is the grouped censored data set of the `n`-th sample (any number `kn n ω` of
distinct observation times, all positive). `Λhat n ω` and `KMhat n ω` are its Nelson–Aalen and
Kaplan–Meier estimates as elements of `ℓ^∞([0, τ])` (`hΛhat`, `hKMhat` tie them to
`CensoredData.nelsonAalen` and `CensoredData.kmSurvival`). `P` is the product integral, given by the
hypothesis `hP` (T77's construction is not imported), and `S = P(-Λ) = ∏_{(0, t]} (1 - dΛ)` is the
survival function of the cumulative hazard `Λ`.

If `√n (Λ̂ₙ - Λ) ⇒ G` in `ℓ^∞([0, τ])` with `-G ∈ closure S` almost surely (`hCLT`, `hG`; the
Nelson–Aalen functional CLT is a hypothesis; for `S` = step functions, `closure S` is the regulated
functions, so `G` may jump, as it does at atoms of the observation-time law) and the negated
Nelson–Aalen paths stay in the domain `D` (`hdom`), then `√n (Ŝₙ - S) ⇒ -Ψ(-Λ, -Λ) G`, i.e.
coordinatewise `-∫_{(0, t]} P(-Λ)(0, s) dG(s) P(-Λ)(s, t]` (through integration by parts, since
`G` need not be of bounded variation). The proof identifies
`Ŝₙ = P(-Λ̂ₙ)` through `IsStieltjesProductIntegral.pureJump` and applies T44's
`MeasureTheory.TendstoInDistribution.functional_delta` with the Hadamard derivative of
`IsStieltjesProductIntegral.hasHadamardDerivWithinAt_neg`.

**Caveat (outer probability / `ℓ^∞` measurability).** This is Borel weak convergence. The
`AEMeasurable` fields of `hCLT` (and `hmeas`) **fail on the canonical space of the observations
whenever the law of the uncensored observation times in `[0, τ]` has a non-atomic part** (T44's
`n = 1` counterexample, see the module docstrings here and of
`MathlibExt.Probability.Statistics.FunctionalDelta`). In that case, which includes every continuous
failure-time distribution with `P(death ≤ τ, uncensored) > 0`, the hypotheses cannot hold and this
theorem says nothing; the classical continuous-time Kaplan–Meier limit there needs the
outer-probability (Hoffmann-Jørgensen) framework, which is not formalized. The theorem can apply
when the uncensored observation (death) times in `[0, τ]` are concentrated on finitely many points
(see the module docstring).

**Caveat (domain).** `hdom` asks for `-Λ̂ₙ ∈ D` almost surely for every `n`. For `D` a
total-variation ball this fails for large `n` unless the death times in `[0, τ]` have finite
support (with `n` distinct deaths `≤ τ`, `Λ̂ₙ(τ) = Hₙ → ∞`); see the module docstring.
