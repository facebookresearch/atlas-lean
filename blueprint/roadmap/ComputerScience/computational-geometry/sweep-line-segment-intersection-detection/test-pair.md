# Testing the neighbours of a deleted segment

Given $n$ segments in the plane over a
linearly ordered field and two optional segment indices $a$ and $b$ (in the sweep, the segments
just below and just above a deleted segment, when they exist), this runs the intersection test
of segments $a$ and $b$ when both indices are present, and otherwise returns `false` at no
cost.
