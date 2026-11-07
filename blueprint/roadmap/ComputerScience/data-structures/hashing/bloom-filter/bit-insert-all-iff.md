# Bits set after inserting a list into a Bloom filter

After inserting a list, bit `i` is set iff it was set before or some hash function sends
some inserted element to `i`.
