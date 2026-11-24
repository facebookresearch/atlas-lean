# Ascending Scan Traced step trace order

One active ascending step records the chosen Lean-model predecessor read,
then the next read, and only then the selected comparison branch.  The access
order is a property of this instrumentation; the comparator orientation is the
source-matching `next < previous`.
