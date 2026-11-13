# Insertion preserves positive answers

Let $F$ be a Bloom filter and let $x$, $y$ be elements.
If $F$ reports that $x$ may be present, then so does the filter obtained by inserting $y$ into $F$.

Insertion never clears a bit, so an element reported present stays reported present after any
later insertion; in particular there are no false negatives under further inserts.
