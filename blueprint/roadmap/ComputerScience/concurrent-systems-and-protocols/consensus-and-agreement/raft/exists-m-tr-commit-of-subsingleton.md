# A single-server Raft cluster elects itself and commits a command

In a cluster with a
single server `i`, for every command `c` there is an execution from the initial state in which
`i` times out, becomes leader of term `1`, receives the client command `c`, sets its
`commitIndex` to `1` and applies `c` at index `1`. At its end `i` is the leader, its log is the
single entry of term `1` and command `c`, and its `commitIndex` and `lastApplied` are `1`.
