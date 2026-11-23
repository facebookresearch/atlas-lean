# Signed breakpoints of a list can differ from those of its doubling

There are a natural number $n$ and a list of integers $\pi$ whose
[signed breakpoint count](sbreaks.md) differs from the [unsigned breakpoint count](ubreaks.md) of
its [doubled list](dbl.md): $b^{\pm}_n(\pi) \ne b_{2n}(\delta(\pi))$. An example is $n = 1$ and
$\pi = (1, 1)$, which repeats an entry: the framed list $(0, 1, 1, 2)$ has one signed breakpoint,
the step from $1$ to $1$, while the doubled list framed by $0$ and $3$, $(0, 1, 2, 1, 2, 3)$, has
none, since the junction $(2, 1)$ of the two doubled copies is one apart. So the
[equality for signed permutations](sbreaks-eq-ubreaks-dbl-of-valid.md) (Shamir and Peer, Lecture 11,
signed setting) needs its hypothesis.
