# Released Temp Storage not live

Regression pinning the liveness boundary: storage explicitly marked
released cannot satisfy the public theorem's live-input premise, irrespective
of any stale `alloced` value that might make the raw reuse comparison true.
