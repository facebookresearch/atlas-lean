# Memmove Backward?

Backward traversal used by `memmove?` for a rightward move, preventing an
overlapping write from destroying an unread source entry.  Exported for direct
trace instrumentation.
