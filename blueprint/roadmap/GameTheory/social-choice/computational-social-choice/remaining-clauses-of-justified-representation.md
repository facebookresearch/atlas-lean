# Justified representation for AV, SAV and MAV

That GreedyAV satisfies justified representation is a separate page (see Related topics). This node collects the
results on approval voting, satisfaction approval voting and minimax approval voting that it does not state.

## Expansion

A sound expansion has separate pages for:

1. **Approval voting:** for committee size $k = 2$, AV satisfies justified representation when ties are broken in favour of committees that
   provide it, and without that tie-breaking assumption it can fail; for every $k \ge 3$ there is an election whose unique AV committee violates
   justified representation (Aziz et al., Theorem 3 and its proof).
2. **SAV and MAV (minimax approval voting):** for every $k \ge 2$ there is an election in which every winning committee violates justified
   representation, whatever the tie-breaking (Aziz et al., Theorem 4 and its proof).

These are existential statements for each committee size; they do not say the rules fail on every election.

## Depends on

- [Approval-based committee elections](approval-based-committee-elections.md)

## Related topics

- [GreedyAV satisfies justified representation](greedyav-satisfies-justified-representation.md)

## Sources

- Justified Representation in Approval-Based Committee Voting — Aziz, Brill, Conitzer, Elkind, Freeman, Walsh, Social Choice and Welfare 48 (2017), Theorems 3 and 4. <https://cgi.cse.unsw.edu.au/~haziz/rep_journal.pdf>
