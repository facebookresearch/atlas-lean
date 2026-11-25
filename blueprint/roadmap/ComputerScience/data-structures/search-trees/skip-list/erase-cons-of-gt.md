# Erasing past a smaller first entry

Let $e$ be a skip-list entry and $L$ a list of
entries. If the key of $e$ is less than a key $k$, then erasing $k$ from the skip list with entry
list $e$ followed by $L$ gives the entry list consisting of $e$ followed by the entry list obtained
by erasing $k$ from the skip list with entry list $L$.
