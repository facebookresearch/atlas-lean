# Sequential rounded summation

For a precision $p$, rounded summation of a list is defined recursively: the empty list sums to $0$, and $x :: xs$ sums to $\mathrm{fl}_p(x + \mathrm{rsum}_p(xs))$, so each partial sum is rounded to $p$ significant bits.
