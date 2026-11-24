# Found New Run Loop Traced unpowered preceding failure

Anti-vacuity regression for the invalid `preceding.power = none` arm.  A
concrete two-run state violates `PoweredPrefix`; the attempted second-last read
is still visible, after which the collapse evaluator returns `none` without a
fuel marker or push.
