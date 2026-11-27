# Extract

Remove the cached minimum, promote its children, and consolidate in rank-indexed bins. Work
counts header removal, one visit per promoted child, an input-root visit and final bin placement
per candidate, one collision probe and link per carry, bin initialisation and final scan over
the whole width (empty bins included), and one minimum comparison per surviving root. Empty
extraction performs just the header check. These are bounded-cost groups of pointer operations.
