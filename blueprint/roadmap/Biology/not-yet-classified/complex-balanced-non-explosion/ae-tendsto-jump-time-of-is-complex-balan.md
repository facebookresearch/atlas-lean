# Complex-balanced stochastic mass-action systems are non-explosive

**Complex-balanced stochastic mass-action systems are non-explosive** (Anderson–Cappelletti–
Koyama–Kurtz 2018, Theorem 3). Let `N` have finitely many species and reactions, let all rate
constants `κ r` be positive, and suppose the deterministic mass-action system is complex balanced
(`N.IsComplexBalanced κ c`) at some `c` with all entries positive. Then the stochastic
mass-action chain `massAction N κ` (`StochasticCRNRegeneration.massAction`, with absorbing
states padded by a rate-`1` fictitious self-loop) is non-explosive from every initial state `x₀`:
almost surely under its step law `inputMeasure`, its jump times `jumpTime x₀` tend to infinity.

## Sources

- D. F. Anderson, D. Cappelletti, M. Koyama, T. G. Kurtz, "Non-explosivity of stochastically modeled reaction networks that are complex balanced", Bull. Math. Biol. 80 (2018) 2561–2579, Theorem 3.
