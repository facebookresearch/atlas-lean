# Iter Ladder

A functional `φ` evaluated on the `i`-th ladder excursion, defined by restarting the path at
the first descending ladder epoch: `iterLadder φ 0 x = φ x` and
`iterLadder φ (i + 1) x = iterLadder φ i (pathShift (descLadderEpoch x) x)`. By
`iterLadder_eq`, `iterLadder φ i x = φ (pathShift (ladderEpoch i x) x)`.
