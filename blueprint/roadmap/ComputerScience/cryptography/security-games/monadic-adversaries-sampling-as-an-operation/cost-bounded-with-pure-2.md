# Cost bound of a pure computation

For every budget $q$ and value $x$, the computation that returns $x$ without any operation is cost-bounded with budget $q$ (for the given costing of operations and continuation predicate) if and only if the continuation predicate holds of $x$ and $q$. The statement is the same whether the pure computation is written with the monad's `pure` or with the free monad's constructor; the two are the same term.
