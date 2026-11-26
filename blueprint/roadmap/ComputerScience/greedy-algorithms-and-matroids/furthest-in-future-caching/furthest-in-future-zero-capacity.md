# Furthest-in-future caching with zero capacity

Run with capacity $0$ on a request
sequence $r_1, \dots, r_n$ from the empty cache, the furthest-in-future manager emits exactly
the events $\mathrm{miss}(r_1), \dots, \mathrm{miss}(r_n)$, one miss per request in order and
each evicting no page, and its final cache is empty.
