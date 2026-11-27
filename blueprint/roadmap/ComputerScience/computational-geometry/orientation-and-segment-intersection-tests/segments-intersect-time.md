# Running time of SEGMENTS-INTERSECT

Let $K$ be a field with a linear order and let
$p_1, p_2, p_3, p_4 \in K^2$. In the cost model that charges one unit per DIRECTION computation
and one per ON-SEGMENT test, SEGMENTS-INTERSECT$(p_1, p_2, p_3, p_4)$ costs at least $4$ and at
most $8$.

The four directions are always computed, and at most four ON-SEGMENT tests run.
