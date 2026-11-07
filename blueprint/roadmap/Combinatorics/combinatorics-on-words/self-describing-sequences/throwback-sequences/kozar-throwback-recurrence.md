# Kozar's conjecture on the throwback sequence

For a sequence
$Y = (Y_0, Y_1, Y_2, \dots)$ of natural numbers, the throwback step produces the sequence $Y'$
with $Y'_i = Y_{i+1}$ for $i < Y_0$, $Y'_{Y_0} = Y_0$, and $Y'_i = Y_i$ for $i > Y_0$: the
leading term $Y_0$ moves to index $Y_0$, the terms $Y_1, \dots, Y_{Y_0}$ shift one place to the
left, and all later terms stay in place. Let $X$ be the sequence with $X_i = i + 3$ (that is,
$3, 4, 5, \dots$), and let $T_k$ be the leading term of the sequence obtained from $X$ by $k$
throwback steps. Then for every natural number $n \ge 3$ and every natural number $N$ there is
$k \ge N$ with $T_k = n$; that is, every $n \ge 3$ equals $T_k$ for infinitely many $k$.

This is Kozar's conjecture for OEIS A357081. Darnell and Dribus prove a more general recurrence
theorem for every sequence of distinct positive integers.

## Sources

- Jesiah Darnell and Benjamin F. Dribus, “Throwback Sequences of Positive Integers”, <https://cs.uwaterloo.ca/journals/JIS/VOL28/Dribus/dribus4.tex>; conjecture/introduction lines 71–80; exact throwback definition lines 98–103; general recurrence theorem and proof lines 124–137.
