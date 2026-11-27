# Erase Chain With Cost time eq

For every key and chain of entries, the counted erasure scan of the chain records the same number of events as the counted lookup scan: one event per unsuccessful comparison before the first match, plus one event for the match or, on a miss, for the empty terminus. A hit does not reach the terminus in either scan.
