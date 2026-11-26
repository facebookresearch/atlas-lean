# Frame property of safe preconditions with separating implication

If `R` does not depend on the variables that `c` modifies (whenever `R s h` holds and `s'` agrees with `s` outside `modVars c`, `R s' h` holds), then `safePre c Q` entails `R -∗ safePre c (Q ∗ R)`.
