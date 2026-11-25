# Fundamental theorem of interval arithmetic and the dependency effect

This node collects the enclosure property of natural interval extensions and its limits.

## Expansion

A sound expansion has separate pages for:

1. **Enclosure.** Intervals are nonempty, closed and bounded, $[a,b]$ with real $a \le b$. For an
   arithmetic expression $e$ in variables $x_1, \dots, x_n$, each of which may occur several times, built
   from $+$, $-$, $\times$ and $\div$, evaluate $e$ on intervals $I_1, \dots, I_n$ by the interval
   operations, where every divisor interval excludes $0$. If the evaluation is defined and gives the
   interval $Y$, then $\{f(x_1, \dots, x_n) : x_i \in I_i\} \subseteq Y$, where $f$ is the function computed
   by $e$ (Lemma 2 of the cited paper).
2. **Single occurrences.** If every variable occurs at most once in $e$, the evaluation is the exact set
   extension of $f$ (Theorem 2 of the cited paper, in its set-valued form).
3. **Dependency effect.** With repeated occurrences the enclosure need not be the range: for $e = x - x$
   and $I = [0,1]$, interval evaluation gives $[0,1] - [0,1] = [-1,1]$ while the range is $\{0\}$.
4. **Width laws.** With width $w([a,b]) = b - a$ and magnitude $\lvert [a,b] \rvert = \max(\lvert a
   \rvert, \lvert b \rvert)$: $w(X \pm Y) = w(X) + w(Y)$ and
   $w(X \cdot Y) \le \lvert X \rvert\, w(Y) + \lvert Y \rvert\, w(X)$, by
   $\lvert xy - x'y' \rvert \le \lvert y \rvert \lvert x - x' \rvert + \lvert x' \rvert \lvert y - y' \rvert$.

These statements use intervals with real endpoints; interval arithmetic with rational endpoints and
directed rounding is the computational special case, with its own enclosure page.

## Sources

- M. H. van Emden and B. Moa, *The fundamental theorems of interval analysis*, arXiv:cs/0701141v2,
  2009, Section 1 (display (1), the enclosure property, and the remark that the enclosing interval is
  typically considerably wider than the range), Lemma 2 (enclosure for arbitrary expressions) and
  Theorem 2 (exact set extension for expressions with single occurrences of each variable). <https://arxiv.org/abs/cs/0701141>
