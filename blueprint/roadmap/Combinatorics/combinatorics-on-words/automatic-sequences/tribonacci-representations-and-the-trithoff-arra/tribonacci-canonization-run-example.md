# Canonizing $2000000$

Words are written most significant digit first. Running at most
two steps of the canonization procedure on the word $2000000$ yields $10001000$.

Both words have value $88$: with $T_n$ the Tribonacci numbers ($T_0 = T_1 = 0$, $T_2 = 1$)
and the digit in position $i$ from the right (starting at $0$) weighted by $T_{i+3}$, they
are $2 T_9 = 2 \cdot 44$ and $T_{10} + T_6 = 81 + 7$. A single Step 2a of the procedure
produces the result.

## Sources

- E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4, Section 6.1.
