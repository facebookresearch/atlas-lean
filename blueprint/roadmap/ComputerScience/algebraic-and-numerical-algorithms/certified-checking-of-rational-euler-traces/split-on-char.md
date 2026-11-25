# Splitting a character list at a separator

For a character `sep`, the split of a list of characters is defined by recursion: the empty list
gives one empty piece; a list starting with `sep` gives an empty piece followed by the split of the
rest; a list starting with another character gives the split of the rest with that character added
at the front of its first piece. The separators are dropped.
