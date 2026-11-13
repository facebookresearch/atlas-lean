# Encrypt-then-MAC is CCA-secure

**Encrypt-then-MAC is CCA-secure** (Katz and Lindell, Section 4.5, encrypt-then-authenticate
with a CPA-secure scheme and a MAC with unique tags): for every CCA adversary making at most `q`
oracle queries,
`ccaAdvantage ≤ cpaAdvantage (cpaReduction A) + ∑_{j < q} macAdvantage (forger j)`.
The sum is Katz and Lindell's `q · ε_Mac` factor, with the guessed index made explicit.
The reductions are admissible query-bounded adversaries: `cpaReduction` makes at most `q`
encryption queries (`cpaReduction_queryBounded`) and every `forger` at most `q + 1` tagging
queries (`forger_queryBounded`).

Hypotheses on the components (needed because framework adversaries are deterministic after
their coins, so the reductions must run them): the encryption scheme has explicit randomness and
decrypts every encryption (`hdec`), and the MAC is deterministic with canonical verification.
