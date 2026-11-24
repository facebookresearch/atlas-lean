# Push Pending Run preserves policy

Full policy postcondition of the actual `list_sort_impl` push.  The
operation mutates unconditionally; the premise proves properties of that
result, including the concrete release-build capacity bound.
