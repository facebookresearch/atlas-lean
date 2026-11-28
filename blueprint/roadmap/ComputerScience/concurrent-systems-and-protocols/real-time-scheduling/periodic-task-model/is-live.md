# Pending requests

Request `k` of task `i` is live, or pending, at slot `t` under a schedule
if it has been made, `release ≤ t`, its deadline has not passed, `t < deadline`, and it has received
fewer than `C` slots of work before `t`. A request whose deadline passes before it receives `C`
slots of work is thus no longer live.
