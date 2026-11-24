# Sort Slice Keys Read?

Instrument a key-array read from the paired `SortSlice` representation.
The returned entry carries the synchronized payload so a caller can reproduce
the uninstrumented atomic representation, but this event records only the key
component.
