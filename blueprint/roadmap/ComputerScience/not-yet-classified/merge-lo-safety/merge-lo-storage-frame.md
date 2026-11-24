# Merge Lo Storage Frame

Exact temporary-storage metadata preserved after `merge_getmem` has
selected the backing used by `merge_lo`.  Payload cells may change during the
initial main-to-temporary copy, so this frame deliberately records their
extent rather than their contents.
