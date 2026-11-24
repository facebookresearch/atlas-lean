# Binarysort safe

Every source-admitted call succeeds, terminates within the source-supplied
`n` fuel, preserves representation mode and extent, and records only in-bounds
key/value accesses.  No ordering law is assumed of the Boolean comparator.
