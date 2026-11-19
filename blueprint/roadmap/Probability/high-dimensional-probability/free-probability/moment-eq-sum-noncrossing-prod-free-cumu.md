# Moment-cumulant formula

For every moment sequence $m$ and every $n \ge 1$,

$$m_n = \sum_{\pi \in NC(n)} \prod_{V \in \pi} \kappa_{|V|},$$

where $\kappa$ are the [free cumulants](free-cumulant.md) of $m$. This is the defining relation of
the free cumulants, recovered from their recursive definition: the term of the one-block partition is
$\kappa_n$, and every other noncrossing partition has blocks of fewer than $n$ elements.

## Informally uses

- [Free cumulants of a moment sequence](free-cumulant.md): the recursive definition being unfolded.

## Sources

- G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010 (numbering of the authors' pre-publication manuscript (2009), https://www.math.nyu.edu/~zeitouni/cupbook.pdf), equation (5.3.5).
