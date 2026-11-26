# Approx Membership Spec

An approximate-membership implementation: states with an empty state, insertion, a possibly over-approximating membership test, and a relation "the state $f$ represents the finite set $S$", such that the empty state represents $\emptyset$; if $f$ represents $S$, then inserting $x$ into $f$ gives a state that represents $S \cup \{x\}$; and if $f$ represents $S$ and $x \in S$, the test reports $x$ present (no false negatives). There is no converse law: the test may report elements that were never inserted, and a state may represent more than one set.
