# Merge Freemem temp Storage Inv

Freeing temporary memory preserves the representation invariant. Inline
storage is unchanged; any non-inline storage enters the released clause, which
requires empty cells but deliberately permits stale `alloced`.
