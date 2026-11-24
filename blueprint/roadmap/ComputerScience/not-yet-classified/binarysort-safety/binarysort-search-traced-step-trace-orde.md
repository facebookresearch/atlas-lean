# Binarysort Search Traced step trace order

An active binary-search step records its midpoint key read first, then the
complete trace of exactly the comparator-selected smaller interval.  Comparator
evaluation itself is deliberately not an access event.
