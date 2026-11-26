# Shared-memory transition rules

Valid scheduled transitions. The operation must be the one chosen by the running process;
its reply determines that process's next local state, and the process halts if that state has
no next operation. An operation can change only the selected object's state and the selected
process's status. A crash is possible only for a running process with a pending operation,
and marks its local state as crashed without changing that state or any shared object.
