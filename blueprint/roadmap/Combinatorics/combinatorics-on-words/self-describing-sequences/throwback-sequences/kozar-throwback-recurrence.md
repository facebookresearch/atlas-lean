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

- Jesiah Darnell and Benjamin F. Dribus, “Throwback Sequences of Positive Integers”, `https://cs.uwaterloo.ca/journals/JIS/VOL28/Dribus/dribus4.tex` (full SHA-256 `91dac9c7d7f6c550c7644258f70d07a03c43f6c7ffc28235addd4dc7598ac86b`); conjecture/introduction lines 71–80 (span SHA-256 `70d48f104dceb3101445c02233f446b984d48e2f9843a23a7ea661e55741e449`); exact throwback definition lines 98–103 (span SHA-256 `6c3a467d42a32e27785634c47c0c2e0ab98cbb5c1b8c8170b0f23ad6d6dfeefc`); general recurrence theorem and proof lines 124–137 (span SHA-256 `fae94ddbaa20aa3fee2d0efef1edd5ee1a73dc13ba62c6053c969a09e915abb5`); concept id `jis_grounded_4375195697bd0ce6cf205efc`.
