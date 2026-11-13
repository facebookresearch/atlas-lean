# Ski-rental upper bound for the break-even strategy

For every purchase price $B \ge 1$ and
every season length $d$, the break-even strategy $\mathrm{breakEven}_B$ pays at most $2 - 1/B$
times the offline optimum $\mathrm{opt}_B(d)$: its cost $\mathrm{cost}_B(\mathrm{breakEven}_B, d)$
for a season of $d$ days satisfies
$B \cdot \mathrm{cost}_B(\mathrm{breakEven}_B, d) \le (2B - 1) \cdot \mathrm{opt}_B(d)$.
