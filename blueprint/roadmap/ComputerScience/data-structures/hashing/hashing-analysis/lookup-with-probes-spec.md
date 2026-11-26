# The result and probe bound of perfect-hash lookup

For any two-level table, the lookup
with probes gives the same result as ordinary lookup. It probes one primary descriptor and at
most one secondary cell: one probe and no result when the selected bucket has zero capacity,
and two probes when its capacity is positive. This statement does not require table validity.
