# While Loop

Let `I` and `Q` be heap assertions. If `I` together with a true
guard entails `safePre body I`, and `I` together with a false guard entails
`Q`, then `I` entails `safePre (.while guard body) Q`. This establishes
fault-avoiding partial correctness; no termination premise is inferred.
