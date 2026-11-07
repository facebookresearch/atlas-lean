# Determinism of evaluation with references

If a configuration $(t, \mu)$ steps to
$(t_1, \mu_1)$ and also to $(t_2, \mu_2)$, then $t_1 = t_2$ and $\mu_1 = \mu_2$.

This relies on allocating each fresh location at the end of the store, at the index equal to the
length of $\mu$; with TAPL's arbitrary choice of fresh location only the result up to renaming of
locations is unique.
