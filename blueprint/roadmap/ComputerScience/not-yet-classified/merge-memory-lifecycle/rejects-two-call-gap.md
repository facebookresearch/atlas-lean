# Rejects two call gap

Two consecutive raw calls cannot validate as one path if the second call
does not start at the first call's recorded final state.  This is the
anti-vacuity regression for history continuity.
