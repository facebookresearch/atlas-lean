# Skip-list levels are sorted by key

If a skip list is valid, then for every level index
$i$ (levels are numbered from $0$ at the bottom), the keys in the list of key-value pairs visible
at level $i$ are strictly increasing: every pair has a strictly smaller key than every pair after
it.
