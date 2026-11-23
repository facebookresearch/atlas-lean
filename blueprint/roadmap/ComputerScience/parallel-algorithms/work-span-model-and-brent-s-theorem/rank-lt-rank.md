# Ranks increase within a level

In a computation DAG, if tasks $u$ and $v$ have the same
depth and $u$ has a smaller number than $v$, then the rank of $u$ is smaller than the rank of
$v$, where the rank of a task is the number of tasks of the same depth with a smaller number.
In particular, ranks are distinct within a level.
