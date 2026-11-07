# Finite-state Markov chain with a given transition matrix

`IsFiniteMarkovChain X P ℱ μ` asserts that the sequence `X : ℕ → Ω → Fin (M+1)`
is a Markov chain with transition matrix `P`, adapted to the filtration `ℱ`,
under the measure `μ`. Concretely: each `X n` is `ℱ n`-measurable, and the conditional
probability that `X (n+1) = j` given `ℱ n` equals `P.prob (X n) j`, matching the
Markov property `P(X_{n+1} = j | X_n = i, ...) = P_{ij}`.
Ported verbatim from `v1/Atlas/TheoryOfProbability/code/FiniteMarkovChain.lean`;
`v1` writes the filtration as `DiscreteFiltration Ω m`, which is `Filtration ℕ m`.
