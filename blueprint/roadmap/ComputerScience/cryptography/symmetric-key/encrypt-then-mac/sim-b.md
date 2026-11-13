# Sim B

The CPA adversary's simulation of the CCA adversary (continuation-passing): encryption
queries are forwarded to the CPA encryption oracle and tagged with the reduction's own MAC key
`k₂`; a decryption query is answered by `simDec` and costs one dummy encryption query, so that
the reduction consumes randomness exactly like the CCA game.
