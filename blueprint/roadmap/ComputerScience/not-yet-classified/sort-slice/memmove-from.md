# Memmove From?

General two-store `sortslice_memmove`.  Same-backing movement delegates to
the overlap-safe shared-store implementation, while a distinct backing follows
the C helper's increasing-address source order.  The branch is selected only by
the explicit provenance constructor, never by comparing stored contents.
