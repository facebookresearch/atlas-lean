# Insertion into an interval tree preserves key ordering

Let $t$ be a key-ordered interval
tree and let $e$ be an entry. Then the tree returned by the cost-instrumented keyed insertion of
$e$ into $t$ (which replaces the entry with the same key, if there is one; the reported cost is
discarded) is again key-ordered.
