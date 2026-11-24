# Ascending Scan?

Scan while each next key is not strictly smaller than its predecessor.
This is used both for CPython's initial ascending attempt and for the final
extension after a descending prefix has been reversed.
