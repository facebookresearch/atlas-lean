# Apply Policy Event?

Apply one raw policy event to an ordered merge forest.

Formed-run metadata is checked before appending a leaf.  A merge checks both
pre-trim operand spans at the recorded index and checks adjacency before
splicing in a node labelled by `replayBoundaryPower`.
