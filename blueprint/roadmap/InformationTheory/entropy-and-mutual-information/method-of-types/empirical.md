# Empirical distribution of a type

Let $\alpha$ be a set of letters. For an $n$-type $s$ (a multiset of $n$ letters), the empirical
distribution is the function $P_s(a) = k_a(s)/n$, where $k_a(s)$ is the number of occurrences of $a$ in $s$.
For $s$ the [type](seq-type.md) of a sequence $x$ it is the relative frequency of each letter in $x$, the
empirical distribution $P_x$; for $n \ge 1$ it is a probability vector
([it sums to one](sum-empirical.md)). For $n = 0$ it is the zero function (with the convention $x/0 = 0$).

The bridge [empirical distribution of a type agrees with the empirical measure](empirical-agrees-with-sample-empirical-measure.md)
identifies it with the empirical measure of a sample, used by the general Sanov theorem.

## Sources

- I. Csiszár, "The method of types", *IEEE Trans. Inform. Theory* 44(6) (1998), 2505–2523, Section II (the type $P_{\mathbf x}(a)$ as the relative frequency of $a$ in $\mathbf x$).
