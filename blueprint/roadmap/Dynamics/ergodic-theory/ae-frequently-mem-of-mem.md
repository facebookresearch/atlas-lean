# Poincaré recurrence theorem

Let $T$ be a measurable map preserving a finite measure $\mu$, and let $E$ be a measurable set. Then for
$\mu$-almost every $x \in E$ there are infinitely many $n$ with $T^n x \in E$: almost every point of $E$
returns to $E$ infinitely often.

The theorem is the first consequence of invariance alone, and it fails without finiteness of the measure:
the translation $x \mapsto x + 1$ of $\mathbb{Z}$ with counting measure preserves the measure, but no point
of $E = \{0\}$ ever returns. The proof goes through conservativity: a map preserving a finite measure is
conservative, and almost every point of a measurable set returns infinitely often under a conservative map.
Its quantitative refinements are the
[Birkhoff ergodic theorem](birkhoff-ergodic-theorem/README.md), which computes the frequency of returns, and
the [Furstenberg multiple recurrence theorem](furstenberg-multiple-recurrence.md), which returns along
arithmetic progressions of times.

## Sources

- O. Sarig, *Lecture Notes on Ergodic Theory* (2023), Theorem 1.1 (Poincaré's Recurrence Theorem) and the example
  $T(x) = x + 1$ on $\mathbb{Z}$ that follows it.
