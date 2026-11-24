# Instrumented search in the empty tree

For every query interval $q$, the instrumented
overlap search of $q$ in the empty interval tree returns no entry, and its cost record counts
one node visit and zero for every other counter (key comparisons, endpoint comparisons,
cached-maximum reads, cache writes, rotations and index operations).
