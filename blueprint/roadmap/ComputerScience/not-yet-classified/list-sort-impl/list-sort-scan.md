# List Sort Scan?

The run-discovery loop.  `lo` and `remaining` replace CPython's moving
`sortslice` pointer and signed counter.  Each successful iteration consumes a
positive run, so `inputSize` units of explicit fuel are sufficient.
