# Universal Bar

Strict total bar `B(M, M, *)` over the same point datum.

The outer factor uses the genuine multiplication `MonObj.mul` as its
explicit right action, with unit and associativity laws supplied directly
by `MonObj.mul_one` and the symmetric form of `MonObj.mul_assoc`. The
inner factor is the same point module as in `classifyingBar`.
