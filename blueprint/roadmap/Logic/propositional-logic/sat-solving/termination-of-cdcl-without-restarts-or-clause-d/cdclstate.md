# CDCL state without restarts

A state of this CDCL model is a pair of a trail (a list of literals, newest first) and a finite set of learned clauses. Unlike the list of learned clauses in the [soundness model](../conflict-driven-clause-learning/state.md), the second component is a set: inserting a clause already present does not change it or its cardinality.
