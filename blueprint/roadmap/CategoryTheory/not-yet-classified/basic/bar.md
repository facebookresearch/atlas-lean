# Barδ

Face map: `d₀` uses `L`, `d_last` uses `R`, interior faces transport.

The definition uses outer `Fin.cases` for zero versus successor and inner
`Fin.lastCases` for last versus `q.castSucc`, so the three branches compute
on `0`, `Fin.last _`, and `q.castSucc.succ`. Branch lambdas are inlined so
this public declaration references no private helpers.
