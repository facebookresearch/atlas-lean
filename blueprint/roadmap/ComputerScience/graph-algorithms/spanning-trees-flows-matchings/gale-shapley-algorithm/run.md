# Running deferred acceptance

Fix rankings for $n$ proposers and $n$ receivers, both
numbered $0, \dots, n-1$. Starting from a state $s$ with a budget of $f$ proposals: if $f = 0$, or
if no proposer is both free (held by no receiver) and has made fewer than $n$ proposals, the run
returns $s$; otherwise the lowest-numbered such proposer makes a proposal, and the run continues
from the resulting state with budget $f - 1$.
