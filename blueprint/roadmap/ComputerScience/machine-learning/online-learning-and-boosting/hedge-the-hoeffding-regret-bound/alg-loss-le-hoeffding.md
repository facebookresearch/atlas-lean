# The Hoeffding regret bound for Hedge

**The Hoeffding regret bound for Hedge** (Cesa-Bianchi and Lugosi, Chapter 2): starting from
unit weights with losses in `[0, 1]` and learning rate `η > 0`, the algorithm's loss over `T`
rounds satisfies `L ≤ L_i + log n / η + η T / 8` against every expert `i`.
