# Merge Hi memcpy Callsite distinct

Every memcpy-class bulk move in `merge_hi` crosses the main and temporary
regions.  The evaluator below couples every such move to one of these tags.
