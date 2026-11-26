# No welfarist committee rule is priceable

An approval election consists of a finite set $N$ of $n$ voters, a finite set $C$ of candidates, approval ballots $A_i \subseteq C$ for $i \in N$, and a committee size $k$ with $1 \le k \le \lvert C \rvert$; a committee is a set $W \subseteq C$ with $\lvert W \rvert = k$. A committee rule is welfarist if there is a function $F$ of the utility vector $(\lvert A_i \cap W \rvert)_{i \in N}$, symmetric and strictly increasing in each coordinate, such that the rule always selects committees maximizing $F$. No welfarist rule always outputs priceable committees; in particular proportional approval voting is not priceable. Moreover no welfarist rule always outputs committees in the core.

## Proof sketch

Construct two elections with identical utility vectors for every committee pair under consideration, so any welfarist rule must treat them identically, while the price-system constraints in the two elections single out different committees. Laminar profiles, where the voter groups form a laminar family, give such examples; the same family shows a core violation for whichever committee a welfarist rule picks.

## Depends on

- [Priceable committee in an approval election](priceable-committee.md)
- [Marginal contributions of a committee under proportional approval voting sum to the number of represented voters](../extended-and-proportional-justified-representation/pav-marginal-contribution-identity.md)

## Proof depends on

- [Priceable committee in an approval election](priceable-committee.md)

## Sources

- D. Peters, P. Skowron, "Proportionality and the Limits of Welfarism", EC 2020, arXiv:1911.11747.
