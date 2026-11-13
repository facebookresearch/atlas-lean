# Gutkovskiy's sequence

Gutkovskiy's sequence (OEIS A286389) is the sequence of natural
numbers $g_0, g_1, \dots$ with $g_0 = 0$ and $g_n = n - g_{\lfloor g_{n-1}/2 \rfloor}$ for
$n \ge 1$ (subtraction of natural numbers, truncated at $0$).

Formally, $g_n$ is defined as $T_n[n]$, the entry at index $n$ of the Gutkovskiy table $T_n$, and
the recurrence is proved from the table.

## Sources

- Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24 (2024), Article A51, Section 1, Equation (1).
