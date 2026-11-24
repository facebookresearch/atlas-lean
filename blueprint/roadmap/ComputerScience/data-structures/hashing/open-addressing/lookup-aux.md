# Bounded lookup scan

Given a table with $m$ slots and probe sequence $p$, a key $k$, a
starting index $s$ and a budget $f$ of probes, examine the slots $p(k, s), p(k, s + 1), \dots$ in
order, for at most $f$ probes. The scan returns the value bound to $k$ in the first examined slot
that holds a binding for $k$, and returns no value if it first reaches an empty slot or exhausts
the budget.

This is the helper behind lookup, which starts at index $0$ with budget $m$.
