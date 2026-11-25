# Operation count of the recursive matrix multiply-accumulate

Let $\alpha$ be a type with
an addition and a multiplication, let $k$ be a natural number and $n = 2^k$, and let $A$, $B$,
$C$ be $n \times n$ matrices over $\alpha$. The recursive multiply-accumulate procedure on $A$,
$B$, $C$ performs exactly $8^k$ scalar multiplications and exactly $8^k$ accumulator additions.
Since $8^k = n^3$, each count is the cube of the dimension.

Calls, indexing and allocation are uncharged.
