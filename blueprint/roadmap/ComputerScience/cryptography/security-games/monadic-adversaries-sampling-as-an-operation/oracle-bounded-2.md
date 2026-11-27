# Query bound of a monadic CPA adversary

A [monadic CPA adversary](mcpaadversary.md) makes at most $q$ encryption queries when its first stage satisfies the [oracle bound](oracle-bounded-with.md) with budget $q$ and the following condition on outputs: at an output $((m_0, m_1), g)$ reached with $j$ queries of budget unused, for **each** possible challenge ciphertext $c$, the second stage $g(c)$ makes at most $j$ encryption queries along every path. So both stages together make at most $q$ encryption queries along every path. Sampling is free.
