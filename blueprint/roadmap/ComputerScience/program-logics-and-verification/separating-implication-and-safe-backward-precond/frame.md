# Frame property of safe preconditions

If `R` does not depend on the variables that `c` modifies (whenever `R s h` holds and `s'` agrees with `s` outside `modVars c`, `R s' h` holds), then `safePre c Q ∗ R` entails `safePre c (Q ∗ R)`: a disjoint frame gives a sufficient precondition for the framed postcondition.
