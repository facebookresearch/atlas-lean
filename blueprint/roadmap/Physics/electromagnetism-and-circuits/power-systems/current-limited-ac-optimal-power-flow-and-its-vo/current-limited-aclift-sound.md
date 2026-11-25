# Soundness of the semidefinite relaxation

Let an [instance](current-limited-opf.md) of the current-limited AC optimal power flow problem with
$n$ buses and $m$ branches be given, with arbitrary data. Then:

- for every [AC-feasible](ac-feasible.md) $V \in \mathbb{C}^n$, the [voltage lift](voltage-lift.md)
  $V V^{\mathsf H}$ is [feasible for the semidefinite relaxation](sdp-feasible.md), and its
  [relaxation cost](sdp-cost.md) equals the [AC cost](ac-cost.md) of $V$;
- every real number $L$ that is at most the relaxation cost of every relaxation-feasible matrix is
  at most the AC cost of every AC-feasible voltage vector.

So dropping the rank-at-most-one property of lifts gives a relaxation whose lower bounds are lower
bounds for the AC problem. If the relaxation has no feasible point, every real $L$ qualifies, and by
the first part no voltage vector is AC feasible. No tightness is claimed: the relaxation can have
feasible points that are not lifts (the [two-bus example](two-bus-rank-two-relaxed-not-lift.md)),
and nothing is said about optimal values being equal or attained.
