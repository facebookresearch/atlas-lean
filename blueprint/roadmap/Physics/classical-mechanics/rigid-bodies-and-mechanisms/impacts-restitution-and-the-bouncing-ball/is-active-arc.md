# Active arc of the bouncing ball

For real `e`, `u₀` and an arc index `n`, arc `n` is active when its
[take-off speed](bounce-speed.md) `u_n` is positive, so that the ball leaves the floor. An arc with
take-off speed `0` is no flight: the ball rests on the floor. The contacts of the bounce sequence
are the ends of its active arcs; an index whose arc is not active is rest, not a further impact.
