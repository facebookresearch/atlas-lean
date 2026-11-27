# Encoded thermal trace checker

An encoded trace (a list of characters) is accepted when trace decoding returns a list $y$ of rationals and the thermal trace checker accepts $y$ (eleven entries, $y_0 = 1$, $y_{j+1} = \tfrac{9}{10} y_j$ for $j = 0, \dots, 9$); it is rejected when decoding returns none. On a concrete input the result is a closed Boolean computation.
