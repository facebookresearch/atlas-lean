# Local alignment with its bounds

The output of a local traceback: the bounds of an infix
`(xs.take xEnd).drop xStart` of a first sequence `xs`, the bounds of an infix
`(ys.take yEnd).drop yStart` of a second sequence `ys`, and an alignment. The structure does not
constrain its fields; `swTraceback_spec` proves that `swTraceback` returns valid bounds and an
alignment of the two infixes.
