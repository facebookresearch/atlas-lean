# Merge Memory Tail

The trace segment produced from an active listsort state through its exit
contains a continuous sequence of real merge calls followed by exactly one
terminal cleanup.  Initialization is added only by `listSortImplTraced?`.
