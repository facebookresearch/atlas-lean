# McNemar's test with a random number of discordant pairs

Let `X ω` and `Y ω` count the
discordant pairs of the two types. If, given each number `X + Y = N` of discordant pairs of
positive probability, `X ~ Bin(N, 1/2)`, then the McNemar p-value at the observed number of
discordant pairs, `ω ↦ P(Bin(X ω + Y ω, 1/2) ≥ X ω)`, is valid under `μ`.

The conditional law is a hypothesis. The Poissonized model does not need it:
`isValidPValue_mcnemarPValue_total` gets validity there from
`GLM.CountData.isValidPValue_countExactPValue`. In the model with a fixed number of pairs and
multinomial cell counts the conditional law is **not** derived here, and that model is reachable
only through this hypothesis.
