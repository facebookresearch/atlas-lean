# Lookup with a cell-probe count

Probe the primary bucket descriptor and, only if its
secondary capacity is positive, the one secondary slot selected by its hash. Return the value
exactly if that slot holds a binding with the query key, and return no value otherwise. The
second component counts one probe for a zero-capacity bucket and two for any other bucket.
Hash computation and key comparison are not charged as cell probes.
