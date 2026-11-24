# Ascending Scan Traced?

Traced ascending scan.  The instrumentation chooses a predecessor-first
read order, while the comparison itself has CPython's `next < previous`
orientation.
