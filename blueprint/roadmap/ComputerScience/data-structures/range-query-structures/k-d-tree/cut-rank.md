# Binary search for a rank cut

Search the slice starting at `start` of length `len`
for the first key failing `pass`, returning its index (or the end) when the slice is in bounds
and the passing keys form a prefix. A missing array entry fails the test. The second result
counts one per midpoint probe and one for the terminal empty slice.
