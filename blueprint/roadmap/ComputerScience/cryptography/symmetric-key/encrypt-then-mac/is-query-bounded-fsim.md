# Query bound of the forger's simulation

The forger's simulation asks the MAC oracle only on encryption queries. So if the adversary
satisfies the two-phase query bound with condition $C$ and budget $N$, and the final stage makes at
most $i + e$ queries whenever $C$ holds with budget $i$, then the simulation makes at most $N + e$
queries.
