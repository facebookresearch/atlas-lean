# CDCL transition

For an input CNF formula $F$, a CDCL state consists of a trail of decided or propagated literals, a list of learned clauses (the current clause set is $F$ followed by them), and an optional conflict clause. One transition is one of:

- **Decide**: with no conflict, set a literal whose variable occurs in $F$ and is unassigned.
- **Propagate**: with no conflict, for a current clause containing $\ell$, if every literal of the clause other than $\ell$ is false on the trail and the variable of $\ell$ is unassigned, add $\ell$ with that clause as its reason.
- **Conflict**: with no conflict, a current clause false on the trail becomes the conflict clause.
- **Resolve**: if the most recent trail entry is a propagated literal $\ell$ with reason $R$ and the complement of $\ell$ is in the conflict clause $C$, replace $C$ by the [resolution of $R$ and $C$ on $\ell$](resolve-on.md) and pop the entry.
- **Skip**: if the most recent trail entry is a propagated literal whose complement is not in the conflict clause, pop it.
- **Backjump**: for a literal $\ell$ of the conflict clause, learn the conflict clause, cut the trail back to a suffix on which every literal of the clause other than $\ell$ is false and the variable of $\ell$ is unassigned, propagate $\ell$ with the learned clause as reason, and clear the conflict.
- **Learn**: add any clause that is resolution-derivable from the current clause set.
- **Restart**: with no conflict, clear the trail and keep the learned clauses.
