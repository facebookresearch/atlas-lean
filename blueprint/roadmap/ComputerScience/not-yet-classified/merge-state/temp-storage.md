# Temp Storage

Temporary merge storage. The outer `Option` represents an allocated slot
whose C contents have not yet been initialized; an entry's own optional value
represents the independent `a.values == NULL` choice. The raw structure admits
arbitrary field combinations; `TempStorageInv` in the adjacent support module
characterizes the representation states reachable from `merge_init`.
