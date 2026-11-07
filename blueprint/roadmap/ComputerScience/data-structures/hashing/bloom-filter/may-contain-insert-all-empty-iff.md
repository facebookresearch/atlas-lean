# Characterization of the Bloom filter false-positive event

The false-positive event: after inserting `xs` into an empty filter, `y` is reported
present iff every bit selected by `y` is selected by some stored element.
