# Sortslice Reverse Traced?

Traced `sortslice_reverse`: complete key reversal first, then the complete
synchronized-values reversal from the same pre-state when values are present.
Both phases execute the paired snapshot update; the second phase's result is
the same reviewed reversal, while its events represent the second C array.
