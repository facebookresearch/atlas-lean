# Routing protocols

In distance-vector routing, neighbors exchange only their estimates of distances. After a link fails, two nodes can then route through each other and raise their estimates without bound, counting to infinity. Protocols stop the count at a fixed bound, 16 hops in RIP, and the same effect delays convergence when an alternative path of large cost exists. Split horizon and poison reverse prevent this between two nodes but not around longer loops; hold-down timers and path information in advertisements are other mitigations (A. C. Snoeren, Distance-vector Routing, Lecture 13 of CSE 123, UC San Diego, Fall 2010, slides 13 to 18).

- [Distance-vector round](step.md)
- [Count-to-infinity in distance-vector routing](count-to-infinity-in-distance-vector-routing.md)
- [Split horizon and poison reverse in distance-vector routing](split-horizon-and-poison-reverse.md)
