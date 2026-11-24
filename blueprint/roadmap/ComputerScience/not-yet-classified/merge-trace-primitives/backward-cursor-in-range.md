# Backward Cursor In Range

Backward merge cursors may be at a live cell or at the one-before-beginning
sentinel produced after copying cell zero.  A dereference still requires the
stronger `0 ≤ cursor` fact.
