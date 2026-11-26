# Bounds, validity and score of the local traceback

For every `σ` and `gap`, the
Smith–Waterman traceback returns bounds `xStart ≤ xEnd ≤ |xs|` and `yStart ≤ yEnd ≤ |ys|` and an
alignment of the infixes `(xs.take xEnd).drop xStart` and `(ys.take yEnd).drop yStart` that scores
`swTab`, the largest cell of the table.
