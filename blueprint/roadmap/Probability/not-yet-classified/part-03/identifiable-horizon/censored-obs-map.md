# Censored Obs Map

The **observation map** of right-censored data on the grid: from the event and censoring times
`(T, C)` one observes the follow-up index `min T C` and the event flag `1[T ≤ C]` (ties count as
events, as in `obsEventMass`).
