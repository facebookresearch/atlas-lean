# Queue3 Cost

Note the asymmetry in Isabelle's cost: `Deq` charges
`size xs + (size ys - 1)` when it has to balance, i.e. it charges
for the elements it moves.
