# Stable polynomials are Lorentzian

For all $n$ and $d$, every homogeneous stable polynomial of degree $d$ in
$\mathbb{R}[w_1, \dots, w_n]$ with nonnegative coefficients lies in the set $L^d_n$ of
Lorentzian polynomials.

For $d \le 2$ this holds by the definition of $L^d_n$. In general it is Brändén and Huh's
Proposition 2.2, whose proof shows by induction on $d$ that strictly stable polynomials are
strictly Lorentzian, starting from quadratic forms (Lemma 2.5) and using that partial
derivatives preserve stability. Since all nonzero coefficients of a
homogeneous stable polynomial have the same sign, every homogeneous stable polynomial is a
constant multiple of a Lorentzian one; the converse fails (Example 2.3 of the paper:
$2w_1^3 + 12 w_1^2 w_2 + 18 w_1 w_2^2 + \theta w_2^3$ is Lorentzian for $0 \le \theta \le 9$
but stable only for $0 \le \theta \le 8$).

## Background

- [Stable homogeneous polynomials with nonnegative coefficients](s.md): the set $S^d_n$ used in
  the statement.
- [The set of Lorentzian polynomials](l.md): the set $L^d_n$.

## Sources

- P. Brändén and J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020), 821–891,
  Proposition 2.2 and Example 2.3, https://arxiv.org/abs/1902.03719.
