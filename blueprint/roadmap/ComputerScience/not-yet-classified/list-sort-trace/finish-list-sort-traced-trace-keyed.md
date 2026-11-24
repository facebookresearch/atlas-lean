# Finish List Sort Traced trace keyed

In keyed mode, an active final reverse records the complete
synchronized-values trace followed by exactly the cleanup boundary formed
from the post-reversal state actually passed to `mergeFreemem`.  It is the C
`reverse_slice(saved_ob_item, ...)` call, not another two-phase
`sortslice_reverse`.
