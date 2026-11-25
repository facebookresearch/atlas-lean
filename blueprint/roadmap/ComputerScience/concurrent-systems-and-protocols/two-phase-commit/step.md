# Transitions of two-phase commit

The protocol steps from a global state $s$ to a
global state $t$ by an action exactly in the following cases. A working participant $p$ may vote
yes, after which $p$ is prepared, or vote no, after which $p$ is aborted. If the coordinator is
waiting and every participant is prepared, the coordinator may decide commit, after which it is
committed. If the coordinator is waiting, it may decide abort, after which it is aborted. If the
coordinator has committed, a prepared participant $p$ may learn the commit, after which $p$ is
committed. If the coordinator has aborted, a prepared or working participant $p$ may learn the
abort, after which $p$ is aborted. In each step every other part of the state is unchanged.
