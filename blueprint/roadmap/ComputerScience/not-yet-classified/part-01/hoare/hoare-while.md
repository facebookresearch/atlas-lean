# Hoare while

While rule: the annotated invariant `I` holds at entry and is
preserved by the body, so it holds at exit together with `¬ b`.
Proved by induction on the `BigStep` derivation, with the loop
identified by an equality hypothesis so the recursor's non-while
cases are discharged by constructor clash.
