# Deterministic post-processing of a mechanism

Given a function $g$ from outputs to new outputs and a mechanism $M$ with values in probability mass functions, the post-processed mechanism sends a database $d$ to the push-forward of $M(d)$ along $g$:

$$
(g \circ M)(d)(o') = \sum_{o \,:\, g(o) = o'} M(d)(o).
$$

It is again a probability mass function.
