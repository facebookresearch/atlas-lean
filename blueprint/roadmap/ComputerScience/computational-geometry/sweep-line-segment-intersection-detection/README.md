# Sweep-line segment intersection detection

## Non-vertical segments as graphs

- [Height of a line at an abscissa](line-y.md)
- [A non-vertical segment is the graph of its line](mem-segment-iff-line-y.md)
- [DIRECTION as a scaled vertical offset](direction-eq-line-y.md)
- [Crossing of two non-vertical segments](exists-mem-inter-of-cross.md)
- [Leftmost point of the intersection of two segments](exists-leftmost-mem-inter.md)

## Sorted lists of graphs

- [Inserting into a strictly sorted list](pairwise-take-while-append-cons-drop-whi.md)
- [Inserting into a weakly sorted list](pairwise-take-while-append-cons-drop-whi-2.md)
- [First element at or above a uniquely attained height](head-drop-while-eq-of-unique.md)
- [Splitting a list at two distinct members](exists-append-of-mem-of-mem.md)

## The algorithm

- [Left endpoint of a segment](left.md)
- [Right endpoint of a segment](right.md)
- [Sweep event](event.md)
- [Endpoint of an event](point.md)
- [Sweep order on endpoint events](key.md)
- [Sorted sweep events](events.md)
- [Segment strictly below a point](below.md)
- [Intersection test for two input segments](test.md)
- [Testing a segment against an optional neighbour](test-opt.md)
- [Testing the neighbours of a deleted segment](test-pair.md)
- [The any-segments-intersect sweep](sweep.md)
- [One step of the sweep](step.md)
- [Running the sweep over a list of events](run.md)

## Endpoints and events

- [Left endpoint events precede right endpoint events](key-left-lt-right.md)
- [A sweep prefix with a right endpoint has its left endpoint](left-mem-of-right-mem.md)

## Invariants of the status list

- [Splitting a list at the first occurrence of a member](take-while-append-cons-tail-drop-while.md)
- [The sweep status holds the active segments](run-mem-iff.md)
- [Meeting segments](meets.md)
- [Neighbours on the sweep status are disjoint](run-is-chain.md)
- [Soundness of the any-segments-intersect sweep](exists-meets-of-run-eq-none.md)

## Completeness

- [The sweep order persists before the leftmost intersection](pairwise-lt-of-pairwise-lt.md)
- [The sweep order holds weakly at the leftmost intersection](pairwise-le-of-pairwise-lt.md)
- [Phase one: the status list is strictly sorted between the processed and remaining events](run-pairwise-lt.md)
- [The status list is weakly sorted after the events left of a vertical line](run-pairwise-le-of-lt.md)
- [Phase two: inserting left endpoints on a vertical line keeps the status weakly sorted](run-pairwise-le.md)
- [Sweep completeness when the leftmost intersection is inside both segments](run-eq-none-of-lt.md)
- [Sweep completeness when the leftmost intersection is a left endpoint](run-eq-none-of-left.md)
- [A leftmost intersection point](exists-leftmost-meet.md)
- [Completeness of the segment-intersection sweep](run-eq-none-of-meets.md)

## Cost

- [Cost charged to a sweep event](event-cost.md)
- [ANY-SEGMENTS-INTERSECT](any-segments-intersect.md)
- [Correctness of ANY-SEGMENTS-INTERSECT](any-segments-intersect-ret-eq-true-iff.md)
- [Running time of ANY-SEGMENTS-INTERSECT](any-segments-intersect-time-le.md)
