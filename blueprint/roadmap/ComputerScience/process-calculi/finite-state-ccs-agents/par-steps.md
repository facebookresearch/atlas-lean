# Code-level parallel composition

Given functions $s$ and $t$ listing the labelled
transitions of codes $x$ and $y$, the transitions of the pair $(x, y)$ are listed in three
blocks: $(a, (x', y))$ for each entry $(a, x')$ of $s(x)$; then $(a, (x, y'))$ for each entry
$(a, y')$ of $t(y)$; then $(\tau, (x', y'))$ for each entry $(a, x')$ of $s(x)$ and each entry
$(b, y')$ of $t(y)$ whose labels are complementary, that is, one is the input and the other the
output on the same name.
