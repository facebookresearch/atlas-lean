# Stable matching mechanisms and incentives

A *matching mechanism* maps every stated preference profile of a marriage market to a perfect matching. Roth (1982) asks which mechanisms can at once be *stable* (always return a stable matching for the stated profile) and give agents the incentive to state their true preferences. His answers: no stable mechanism makes truth-telling a dominant strategy for every agent (Theorem 3), but the mechanism returning the man-optimal stable matching makes it dominant for every man (Theorem 5), and that matching is weakly Pareto optimal for the men among all matchings (Theorem 6). The model is Roth's: two sides of equal size, complete strict preferences, perfect matchings.

## Mechanisms and incentives

- [Matching mechanism](matching-mechanism.md)
- [Stable matching mechanism](is-stable-mechanism.md)
- [Truthful revelation is dominant for a man](is-truthful-dominant-for-man.md)
- [Truthful revelation is dominant for a woman](is-truthful-dominant-for-woman.md)
- [Strategy-proof matching mechanism](is-strategy-proof.md)
- [Man-optimal stable matching](is-man-optimal-stable.md)
- [Every market with sides of equal size has a man-optimal stable matching](exists-is-man-optimal-stable.md)
- [Uniqueness of the man-optimal stable matching](man-optimal-stable-matching-unique.md)
- [Stability without the inverse matching](is-stable-iff-forall-partner.md)

## Roth's impossibility theorem

- [Roth's impossibility theorem](not-exists-stable-strategy-proof.md)
- [In Roth's market every stable mechanism is manipulable](roth-stable-mechanism-manipulable.md)
- [Roth's market has exactly the two stable matchings $x$ and $y$](roth-is-stable-iff.md)
- [After $m_1$'s misreport, $x$ is the unique stable matching](roth-is-stable-man-misreport-iff.md)
- [After $w_1$'s misreport, $y$ is the unique stable matching](roth-is-stable-woman-misreport-iff.md)

### Roth's market

- [Men's ranks in Roth's market](roth-men-rank.md)
- [Women's ranks in Roth's market](roth-women-rank.md)
- [Men's preferences in Roth's market](roth-men-prefs.md)
- [Women's preferences in Roth's market](roth-women-prefs.md)
- [Man $m_1$'s misreport in Roth's market](roth-man-misreport-rank.md)
- [Man $m_1$'s misreported preference](roth-man-misreport.md)
- [Woman $w_1$'s misreport in Roth's market](roth-woman-misreport-rank.md)
- [Woman $w_1$'s misreported preference](roth-woman-misreport.md)
- [The men-preferred stable matching $x$ of Roth's market](roth-x.md)
- [The women-preferred stable matching $y$ of Roth's market](roth-y.md)
- [Preference given by a rank function](rank-order.md)
- [The ranking $a \succ b \succ c$ on three agents](rank3.md)
- [Stability read off ranks on three agents](stable-by-ranks.md)

## The man-optimal stable mechanism

- [Strategy-proofness of the man-optimal stable mechanism for the men](man-optimal-mechanism-strategy-proof-for-men.md)
- [Weak Pareto optimality of the man-optimal stable matching for the men](not-forall-lt-of-is-man-optimal-stable.md)
- [Strategy-proofness of deferred acceptance with unequal sides and unacceptable partners](deferred-acceptance-with-unacceptable-partners-and-unequal-sides.md)
- [Slot](slot.md)
- [Slot Index](slot-index.md)
- [Student Prefs](student-prefs.md)
- [Slot Prefs](slot-prefs.md)
- [Roster](roster.md)
- [Mem roster](mem-roster.md)
- [Assignment](assignment.md)
- [Blocks](blocks.md)
- [Is Stable](is-stable.md)
- [Roster eq empty of quota zero](roster-eq-empty-of-quota-zero.md)
- [Not blocks of quota zero](not-blocks-of-quota-zero.md)
- [Collapse](collapse.md)
- [Rank](rank.md)
- [Rank lt card](rank-lt-card.md)
- [Assigned Slot](assigned-slot.md)
- [Lift](lift.md)
- [Lift eq some iff](lift-eq-some-iff.md)
- [Collapse lift](collapse-lift.md)
- [Ordered](ordered.md)
- [Ordered lift](ordered-lift.md)
- [Ordered of stable](ordered-of-stable.md)
- [Occupied iff lt roster card](occupied-iff-lt-roster-card.md)
- [Lift collapse of ordered](lift-collapse-of-ordered.md)
- [Stable collapse](stable-collapse.md)
- [Stable lift iff](stable-lift-iff.md)
- [Many-to-one stable matching reduces to one-to-one by quota slots](college-admissions-reduces-to-marriage.md)

## Related topics

- [Lattice of stable matchings](../lattice-of-stable-matchings/README.md): the structure of the set of stable matchings, in which the man-optimal stable matching is the top element for the men.
- [Gale–Shapley algorithm](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/gale-shapley-algorithm/README.md): deferred acceptance computes the man-optimal stable matching, so it implements the mechanism of Roth's Theorem 5.
- [Gibbard–Satterthwaite theorem](../../social-choice/gibbard-satterthwaite-theorem/README.md): the impossibility theorem for social choice functions that Roth's Theorem 3 parallels (Roth 1982, §1).
- [Mechanism design](../../mechanism-design/README.md): dominant-strategy incentive compatibility and the revelation principle for mechanisms with cardinal utilities; the strategy-proofness here is the ordinal, matching-specific counterpart.
