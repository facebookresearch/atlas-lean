# No welfarist committee rule is priceable

An approval election consists of a finite set $N$ of $n$ voters, a finite set $C$ of candidates, approval ballots $A_i \subseteq C$ for $i \in N$, and a committee size $k$ with $1 \le k \le \lvert C \rvert$; a committee is a set $W \subseteq C$ with $\lvert W \rvert = k$. A committee rule is welfarist if for each $k$ there is a function $g_k$ of the welfare vector $(\lvert A_i \cap W \rvert)_{i \in N}$ such that the rule always selects the committees maximizing $g_k$; it is Pareto optimal if each $g_k$ is monotone. No Pareto-optimal welfarist rule always outputs priceable committees; in particular proportional approval voting is not priceable. Moreover no welfarist rule, Pareto optimal or not, always outputs committees in the core.

## Proof sketch

For priceability, take a profile with $12$ voters and committee size $57$ in which every voter approves at least $57$ candidates. The price-system constraints bound the number of representatives of some voters and force the representation of others, which restricts the welfare vectors of priceable committees; the profile is built so that a Pareto-optimal welfarist rule must select a committee whose welfare vector is not of this form, a contradiction. For the core, take a profile with $16$ voters, $54$ candidates and $k = 48$ in which the core forces specific candidates for several voter groups; comparing welfare vectors of committees that the rule cannot distinguish shows that whichever committee it picks, some group can block it.

## Depends on

- [Priceable committee in an approval election](priceable-committee.md)
- [Core of an approval-based committee election](core-of-approval-committee-election.md)
- [Thiele methods for approval committee elections](../extended-and-proportional-justified-representation/thiele-methods.md)

## Sources

- D. Peters, P. Skowron, "Proportionality and the Limits of Welfarism", EC 2020, arXiv:1911.11747.
