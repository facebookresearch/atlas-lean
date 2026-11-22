# Sorted sweep events

For $n$ segments, each given by its two endpoints, the left endpoint
of a segment is its endpoint with the smaller $x$-coordinate, or its first given endpoint when
both $x$-coordinates agree, and the right endpoint is the other one. The event list consists of
the $2n$ events, the left and the right endpoint of each segment, sorted by the $x$-coordinate
of the endpoint, with left endpoints before right endpoints at equal $x$, and then by the
$y$-coordinate of the endpoint; events that tie appear in increasing order of segment index.
This is line 2 of CLRS ANY-SEGMENTS-INTERSECT.
