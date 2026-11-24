# Merge Lo Memcpy Data To Temp initialized of eq some

A successful data-to-temporary bulk copy initializes its whole destination
range.  In particular, this discharges the totality precondition of
`mergeLoTempRun_exists_of_initialized` for the initial `merge_lo` copy.
