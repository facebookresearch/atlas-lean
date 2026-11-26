# Is Feasible Schedule

A feasible event schedule: nonnegative model-event times and every precedence
constraint. Unlike `MathlibExt.Combinatorics.Graph.ArcNetwork.IsFeasibleSchedule`, which has
`ℕ` times over an arc type, times here are integers over the `BellmanFord` occurrence list
that the runs read, so nonnegativity on model events is part of the definition. (`C9`)
