# Finite-window work-in-process balance

Consider finitely many operations connected by routing edges, through which batches with unique identities move, each material
counted on one basis. Assume each operation obeys the local inventory balance: its stock change is its incoming amount minus
its outgoing amount, with no generation, consumption or unaccounted loss of the tracked material. Count every boundary outflow
as good output or scrap. Use the same amount for each internal transfer at its sending and receiving operations. Summing these
local balances cancels all internal transfers. Over a window $[0, T]$, the input to the system therefore equals the good output plus the scrap
plus the change of work in process, $\mathrm{WIP}(T) - \mathrm{WIP}(0)$. A rework edge returns material from one operation to
another inside the system, so it is never new supply and does not enter the input. The balance holds even when all output is
reworked, in which case nothing leaves as good output or scrap and the work in process absorbs the whole input. Steady
throughput of a rework loop is a separate result. Unique batch identities alone do not imply the local conservation law.
If the tracked species is produced or consumed, include its signed net production on the input side of this balance instead.

## Depends on

## Proof depends on

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 4.3, Equation 4.36, the species balance with accumulation, flows and production (p. 127).
