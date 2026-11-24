# List Sort Scan Collapse Correctness Post

Complete correctness certificate for a `listSortScan?` execution.

`terminal` is the state at the real `remaining = 0` call, `collapsed` is the
result returned by the real `mergeForceCollapse?` invocation there, and
`result` is the state after the requested final-reverse/cleanup phase. Retaining
all three keeps the pre-finish sorted/stable run available even though final
reversal changes its order and cleanup may release temporary storage.
