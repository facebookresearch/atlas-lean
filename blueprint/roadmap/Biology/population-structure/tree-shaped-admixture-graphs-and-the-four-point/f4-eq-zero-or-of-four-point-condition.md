# F4 eq zero or of four Point Condition

If `f2` satisfies the four-point condition (as the `f2` matrix of a tree
model does, by `Buneman.IsTreeMetric.fourPointCondition`), then for every
four populations at least one of the three f4 permutations
`f4(A,B;C,D)`, `f4(A,C;B,D)`, `f4(A,D;B,C)` vanishes. The four-point
condition says each of the pair sums `S1 = f2AB+f2CD`, `S2 = f2AC+f2BD`,
`S3 = f2AD+f2BC` is at most the maximum of the other two, so two of them are
equal, and the f4 permutations are the half-differences of the pair sums.
