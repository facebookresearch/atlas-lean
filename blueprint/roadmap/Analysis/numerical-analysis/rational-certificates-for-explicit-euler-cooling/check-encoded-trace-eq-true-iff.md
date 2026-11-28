# Encoded trace acceptance is decoding followed by the trace checker

For a list of characters $s$, the encoded trace checker accepts $s$ if and only if there is a list $y$ of rationals such that trace decoding of $s$ returns $y$ and the thermal trace checker accepts $y$.

A list $y$ of rationals is accepted by the thermal trace checker when it has exactly eleven entries $y_0, \dots, y_{10}$, $y_0 = 1$, and $y_{j+1} = \tfrac{9}{10}\, y_j$ for $j = 0, \dots, 9$.
