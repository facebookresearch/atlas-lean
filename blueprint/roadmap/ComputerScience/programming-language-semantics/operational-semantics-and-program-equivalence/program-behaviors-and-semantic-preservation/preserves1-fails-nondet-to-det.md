# Form (1) preservation fails from the nondeterministic to the deterministic toy

Preservation in form (1), every behavior of the source is a behavior of the target, fails from the nondeterministic toy to the deterministic toy when both start at configuration `a`: the source terminates at `b2` with trace `[false]`, which the target, whose only step from `a` is labelled `true`, cannot do. Started at `b1` instead, both systems have the same terminating empty trace.
