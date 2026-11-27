# Query budget of the baby steps

Let `1 < q`. If every continuation `G p` makes at most `t` queries, then the
baby-step loop `babiesAux f cur g acc` with fuel `f` stays within budget `t +
f`, leaving at every output `p` budget `j` from which `G p` makes at most `j`
queries: the baby steps use exactly the fuel as queries.
