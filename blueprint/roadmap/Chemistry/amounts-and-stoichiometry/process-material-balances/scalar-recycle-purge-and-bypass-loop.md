# Scalar recycle, purge and bypass loop

Consider steady flows of one conserved quantity.

1. **Recycle.** If the loop flow satisfies $f = f_0 + r f$ with fresh feed $f_0 \ge 0$ and returned fraction $0 \le r < 1$, then
   $f = f_0/(1 - r)$. For $r = 1$ there is no finite solution when $f_0 > 0$, and every $f$ solves the equation when $f_0 = 0$.
2. **Purge.** If an inert species enters with fresh feed $a \ge 0$ and leaves only through a purge that removes the fraction
   $0 < p \le 1$ of the loop flow, the loop flow before the split is $a/p$, the purge is $a$, and the returned flow is
   $(1 - p)a/p$.
3. **Bypass.** A stream bypassing a unit with fraction $0 \le b \le 1$ and remixed downstream gives the outlet of an ideal mixer:
   its composition is the flow-weighted convex combination of the bypass and the unit outlet, not a new mixing law.

## Depends on

## Proof depends on

- [Ideal mixer and nonselective splitter](ideal-mixer-and-nonselective-splitter.md), for the bypass

## Sources

- *Introduction to Chemical Engineering Processes*, Wikibooks, chapter "How to Analyze a Recycle System" (splitter balances with equal composition of the outlets), <https://en.wikibooks.org/wiki/Introduction_to_Chemical_Engineering_Processes/How_to_Analyze_a_Recycle_System>.
