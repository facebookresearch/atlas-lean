# Cursor In Range

A pointer-like cursor lies between the beginning of the slice and its
permitted one-past endpoint, inclusive.  Unlike `IndexInBounds`, the upper
endpoint is a valid cursor but cannot itself be dereferenced.
