# Preprocessing a planar range index

Sort by x, attach x ranks, sort the tagged points
by y, then attach y ranks. Scatter the rank pairs into their x order by indexed writes to a
fresh array. Build the tree from the two orders. In addition to tree construction, charge the
key comparisons in both merge sorts, the number of records at their nontrivial splits, ten
linear passes and one setup unit. No sort occurs below the root of the kd-tree.
