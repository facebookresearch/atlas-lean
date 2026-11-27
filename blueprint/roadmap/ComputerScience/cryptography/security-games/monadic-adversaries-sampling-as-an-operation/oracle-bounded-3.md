# Query bound of a monadic CCA adversary

A [monadic CCA adversary](mccaadversary.md) makes at most $q$ oracle queries when its first stage satisfies the [oracle bound](oracle-bounded-with.md) with budget $q$ and the following condition on outputs: at an output $((m_0, m_1), g)$ reached with $j$ queries of budget unused, for **each** possible challenge ciphertext $c$, the second stage $g(c)$ makes at most $j$ oracle queries along every path. Encryption and decryption queries both count; sampling is free.
