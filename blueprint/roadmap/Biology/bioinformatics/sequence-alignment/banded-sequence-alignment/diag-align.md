# Diagonal alignment

For sequences $x = x_1 \dots x_m$ and $y = y_1 \dots y_n$, let
$k = \min(m, n)$. The diagonal alignment of $x$ and $y$ consists of the columns
$(x_1, y_1), \dots, (x_k, y_k)$, which pair letters by position whether or not they are equal,
followed by one column for each remaining letter of the longer sequence, in order, pairing that
letter with a gap.
