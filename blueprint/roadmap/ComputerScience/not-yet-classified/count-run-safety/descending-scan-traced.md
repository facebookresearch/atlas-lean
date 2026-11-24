# Descending Scan Traced?

Traced descending scan.  It probes `next < previous` first, then
`previous < next`, and delegates every completed equality block to
`reverseLastEqualTraced?`.
