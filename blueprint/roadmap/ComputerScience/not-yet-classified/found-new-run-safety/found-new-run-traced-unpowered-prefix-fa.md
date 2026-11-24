# Found New Run Traced unpowered prefix failure

End-to-end form of the same anti-vacuity regression.  The outer evaluator
passes its source-domain guard, records the current-top read, enters the
collapse loop, records the uninitialized preceding run, and then fails.
