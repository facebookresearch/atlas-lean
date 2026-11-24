# Uniqueness of the reduced row echelon form

Let $K$ be a field, let $m$ and $n$ be finite
linearly ordered sets, and let $R_1$ and $R_2$ be $m \times n$ matrices over $K$ in reduced row
echelon form. If $R_2 = P R_1$ for some invertible $m \times m$ matrix $P$ over $K$, then
$R_1 = R_2$. In other words, a row-equivalence class contains at most one matrix in reduced row
echelon form.

Proof: Reindex the columns along the order isomorphism between $\{0, \dots, |n| - 1\}$ and $n$.
For columns indexed by an initial segment of the natural numbers, induct on the number of
columns: the matrices agree on all but the last column by induction, and that forces their last
columns to agree.

## Sources

- G. Strang, Introduction to Linear Algebra, 6th ed., Wellesley-Cambridge Press (2023), Section 2.2.
