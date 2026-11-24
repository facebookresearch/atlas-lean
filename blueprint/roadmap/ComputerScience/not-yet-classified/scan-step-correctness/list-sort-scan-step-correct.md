# List Sort Scan step correct

One complete nonterminal iteration of the real `listSortScan?` evaluator.
The returned state is exactly the evaluator's recursive-call state, carries
the full semantic scan invariant, and may include any strict-power merges
performed before the unconditional pending-run push.
