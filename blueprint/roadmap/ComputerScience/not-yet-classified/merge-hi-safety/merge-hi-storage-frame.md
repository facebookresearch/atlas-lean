# Merge Hi Storage Frame

Exact temporary-storage metadata preserved after `merge_getmem` has
selected the backing used by `merge_hi`.  The initial copy may replace payload
contents, so the frame records their extent rather than extensional equality.
