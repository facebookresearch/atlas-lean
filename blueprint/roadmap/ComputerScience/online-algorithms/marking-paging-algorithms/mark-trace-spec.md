# Events of a marking run

For every eviction rule, marking state $s$ and request sequence $\sigma$, the events emitted while
serving $\sigma$ from $s$ form a legal run of the paging system from the current cache to the final
one, their requests are exactly $\sigma$, and their number of misses equals the number of misses of
the marking pager on $\sigma$ from $s$.
