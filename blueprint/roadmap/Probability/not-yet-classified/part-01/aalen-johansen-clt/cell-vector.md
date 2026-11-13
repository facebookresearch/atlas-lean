# Cell Vector

The cell indicator vector of one subject `w = ((T, J), C)`: the coordinate `Sum.inl (j, c)`
is `1[min T C = j, T ≤ C, J = c]` and the coordinate `Sum.inr j` is `1[min T C ≥ j]`. Summing it
over subjects gives the cause-specific event counts and the at-risk counts.
