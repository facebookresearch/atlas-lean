# Merge Getmem Non Storage Frame

Every `MergeState` field that `merge_getmem` must frame.  Temporary
storage and its capacity are intentionally absent because growth replaces
exactly those two fields.
