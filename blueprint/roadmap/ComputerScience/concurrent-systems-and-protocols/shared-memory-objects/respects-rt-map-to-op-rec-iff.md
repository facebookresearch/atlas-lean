# Completed-operation records preserve real-time order constraints

A list of completed operations of one finite history respects the history's real-time
order (no later entry precedes an earlier one) if and only if its list of `OpRec` exports
satisfies `RespectsRT`. The supplied payload encodings are arbitrary, and the equivalence
does not require distinct list entries.
