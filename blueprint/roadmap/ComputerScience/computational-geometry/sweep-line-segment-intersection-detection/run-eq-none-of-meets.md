# Completeness of the segment-intersection sweep

Let $n$ segments in the plane over a
linearly ordered field be given, none of them vertical (the left endpoint of each has strictly
smaller abscissa than its right endpoint), and assume, as CLRS does, that no point lies on three
distinct segments. If two distinct segments meet, then the sweep, run on the sorted list of
endpoint events from the empty status list, reports an intersection.
