# Pieces LE

Bounded piece-count predicate: `PiecesLE n f` holds when `f` satisfies the
collinearity equation on each interval avoiding some breakpoint set `s` with at
most `n` intervals (`s.card + 1` intervals). This captures continuous
piecewise-affine functions: `f` is affine on each closed interval between
consecutive breakpoints, with values agreeing at shared endpoints. This is the
bounded form of the lecture-notes affine-pieces definition for continuous `f`,
so `PiecesLE n f` implies the source piece count of `f` is at most `n`; no
minimality of the breakpoint set is claimed.
