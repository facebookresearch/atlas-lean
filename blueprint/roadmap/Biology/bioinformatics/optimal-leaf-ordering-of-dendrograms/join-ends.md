# Joining two subtree orders at an adjacent leaf pair

For a similarity $S$, tables $M_l, M_r : A \times A \to \mathbb{R} \cup \{-\infty\}$, lists of leaves $L_l, L_r$ and labels $i, j$, put

$$J(i, j) = \max_{k \in L_l,\ l \in L_r} \bigl(M_l(i, k) + S(k, l) + M_r(l, j)\bigr),$$

with $-\infty$ absorbing in sums and the maximum over an empty range equal to $-\infty$.
