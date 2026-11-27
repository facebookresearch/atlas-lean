# First-column recurrence for the continuation after a match

For all letters $a, b$ and sequences $x, y$,

$$M(a x, b y) = \max\bigl(M(x, y) + \sigma(a, b),\ X(x, b y) + o,\ Y(a x, y) + o\bigr),$$

with $M$, $X$, $Y$ the [continuation values](gotoh-cont-none.md) ([after a gap in the second sequence](gotoh-cont-gap-x.md), [in the first](gotoh-cont-gap-y.md)).
