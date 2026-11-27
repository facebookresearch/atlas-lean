# Divergence is an infinite sequence of unlabelled steps

A configuration $c$ [diverges](diverges.md) exactly when there is a sequence $f : \mathbb{N} \to \mathrm{Config}$ with $f(0) = c$ and an unlabelled step from $f(i)$ to $f(i+1)$ for every $i$, each step taken with some label. No particular label stream or fairness condition is prescribed; the labels recovered from the steps are not a claim about any particular action trace.
