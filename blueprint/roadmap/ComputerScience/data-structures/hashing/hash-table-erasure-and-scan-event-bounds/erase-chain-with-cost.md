# Erase Chain With Cost

The counted erasure scan of a chain for a key: on the empty chain it returns the empty chain after one terminal event; on a chain whose head has the key it returns the untouched tail after one event, so only the first match is removed (erasing $k$ from $[(k, a), (k, b)]$ leaves $[(k, b)]$); otherwise it keeps the head, continues on the tail and adds one event.
