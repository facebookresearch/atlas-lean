# Ready To Push stack depth bound

Exact capacity accounting for the actual unconditional push used by
`list_sort_impl`: the old depth is at most 60, the result is exactly one
larger and at most 61, and 61 is strictly below `MAX_MERGE_PENDING = 64`.
