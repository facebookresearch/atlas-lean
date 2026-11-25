# Up-front versus fresh randomness

For an algorithm making at most `n` encryption
queries, answering its `i`-th query with the `i`-th entry of a uniform `ρ : Fin n → X` gives the
same output distribution as sampling fresh randomness per query (`evalPMF`), and never stops
it.
