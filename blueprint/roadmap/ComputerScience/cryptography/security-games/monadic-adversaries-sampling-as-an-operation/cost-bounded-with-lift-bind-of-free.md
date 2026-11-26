# A free operation consumes no budget

If the operation `a` is not costly (`costly a = false`), then `liftBind a k`
is cost-bounded with budget `q` if and only if every continuation `k b` is
cost-bounded with budget `q`.
