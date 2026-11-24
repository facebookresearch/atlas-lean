# Stable Entry Merge append left block

A block whose every entry is strictly after every right-run entry can be
peeled from the end of the left input and appended unchanged after the merge.
The statement is deliberately whole-entry and does not require decidable
equality, so `merge_hi` can apply it directly to galloped payload blocks.
