# Memcpy Traced?

Traced `sortslice_memcpy`.  The backing-domain check occurs before either
physical phase.  On an admissible call the second phase starts from the
original paired store, reflecting that C's key and values arrays are distinct.
