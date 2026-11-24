# Merge Hi Cursor Invariant

Inductive invariant for every live right-to-left merge cursor.  The three
equalities are the subtraction-sensitive core: they retain the legal `-1`
sentinels rather than coercing backward cursors through `Nat`.
