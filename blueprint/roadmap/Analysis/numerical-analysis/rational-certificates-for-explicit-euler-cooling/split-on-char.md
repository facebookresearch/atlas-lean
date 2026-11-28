# Splitting a character list at a separator

For a separator character $s$, the list of characters is split at every occurrence of $s$, dropping the separators: the empty list gives a single empty piece, and a list with $m$ occurrences of $s$ gives $m + 1$ pieces (possibly empty), in order. It is defined by structural recursion: on $c :: cs$, if $c = s$ a new empty piece is put in front of the split of $cs$, and otherwise $c$ is prepended to the first piece of that split.
