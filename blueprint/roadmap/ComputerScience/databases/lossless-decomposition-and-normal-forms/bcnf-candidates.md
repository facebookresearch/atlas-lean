# Candidate BCNF violations

Given a list $l$ of attributes and a set $S$ of attributes, the
candidate violations of BCNF in $S$ are all subsets of the set of attributes that occur in $l$ and
lie in $S$, listed once each. Duplicates in $l$ are removed first, so there are $2^k$ candidates
when $k$ distinct attributes of $l$ lie in $S$.
