# Memcpy?

Copy `count` entries using C `memcpy`'s backing discipline.  Overlapping
same-backing ranges are outside the modeled domain and return `none` before any
copy step; distinct backings are not inferred from their contents.
