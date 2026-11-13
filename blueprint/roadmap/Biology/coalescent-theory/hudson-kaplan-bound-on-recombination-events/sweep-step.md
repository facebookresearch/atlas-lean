# One step of the Hudson–Kaplan sweep

One step of the sweep at right endpoint `j`. The list `acc` holds the intervals kept so far,
most recent first; the next interval must start at or after the right end of the most recent
one (at or after site `0` if none was kept). Among the admissible four-gamete intervals ending
at `j`, the shortest one is kept.
