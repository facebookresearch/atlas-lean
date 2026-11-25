# Interval tree entry

An entry of the interval tree consists of an identifier, which is a
natural number, and an interval with integer low and high endpoints.

Identifiers, rather than endpoints, are meant to be unique among stored entries; this is required
by the indexed tree's representation invariant, not by the entry itself.
