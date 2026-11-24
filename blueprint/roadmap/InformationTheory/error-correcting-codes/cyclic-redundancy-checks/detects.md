# CRC error-detection guarantee

Let $F$ be a field, let $g$ be a polynomial over $F$ with
at least two nonzero coefficients that is not divisible by $X$, let $m$ be a polynomial over $F$,
and let $c$ be the CRC encoding of $m$ with generator $g$. Then $g$ does not divide $c + aX^i$ for
any nonzero $a \in F$ and any natural number $i$, and $g$ does not divide $c + e$ for any
polynomial $e$ over $F$ that is a burst of length at most $\deg g$. That is, the check detects
every single-symbol error and every burst of length at most $\deg g$ in every codeword.

Given $X \nmid g$, having at least two terms is the same as $\deg g \ge 1$, and a single-symbol
error is a burst of length 1.
