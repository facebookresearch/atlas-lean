# The interpolant in the span of the data is unique

If $w$ and $w'$ both lie in the span of the data points and both interpolate the labels, then $w = w'$: their difference lies in the span and is orthogonal to it.

The source phrases this as the uniqueness of the solution $\alpha$ of $X X^\top \alpha = y$ (its equation (3)), which holds when $X$ has rank $n$; uniqueness of $w = X^\top \alpha$ holds without that assumption.

## Sources

- C. Zhang, S. Bengio, M. Hardt, B. Recht and O. Vinyals, *Understanding deep learning requires rethinking generalization*, ICLR 2017, arXiv:1611.03530, Section 5, equation (3).
