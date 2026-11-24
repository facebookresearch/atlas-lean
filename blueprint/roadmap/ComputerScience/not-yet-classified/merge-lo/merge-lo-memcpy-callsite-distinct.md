# Merge Lo memcpy Callsite distinct

Every memcpy-class bulk move in `merge_lo` crosses the main and temporary
regions.  The evaluator below couples every such move to one of these tags.
