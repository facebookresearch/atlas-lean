# Number of rising sequences of an arrangement

Read $\pi \in S_n$ as an arrangement of a deck, card $\pi(i)$ at position $i$. A rising sequence is
a maximal run of consecutive face values $v, v+1, \dots$ lying at increasing positions; for
example $1, 5, 2, 3, 6, 7, 4$ has the two rising sequences $1, 2, 3, 4$ and $5, 6, 7$. The runs
break exactly at the values $v$ whose successor $v + 1$ lies above $v$, that is
$\pi^{-1}(v+1) < \pi^{-1}(v)$, so the number of rising sequences is one plus the number of such $v$.
Equivalently, $\pi$ has $r$ rising sequences iff $\pi^{-1}$ has $r - 1$
descents. This describes nonempty decks; for the empty deck ($n = 0$), which has no runs, the
count one plus the number of breaks is $1$ by convention.

## Sources

- D. Bayer and P. Diaconis, *Trailing the dovetail shuffle to its lair*, Ann. Appl. Probab. 2
  (1992) 294–313, Sections 1–3.
