# A legal trace misses at least once

Let $k$ be a capacity and $C$ a cache listing at most
$k$ pages, and consider a legal trace of cache events for capacity $k$ that starts from $C$. Let
$p$ be a page in $C$. If at least $k + 1$ distinct pages are each equal to $p$ or served by some
event of the trace, then the trace contains at least one miss.
