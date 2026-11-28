# Total result transition system of a STRIPS task

For a STRIPS task, the total result labelled transition system has the sets of true atoms as states and operators as labels. There is a transition from $s$ to $s'$ labelled by an operator $o$ exactly when $o$ is one of the task's operators and $s'$ is the result of $o$ in $s$: $(s \cup A) \setminus D$, for the add set $A$ and delete set $D$ of $o$, when every positive precondition of $o$ holds in $s$ and no negative precondition does, and $s$ itself otherwise.
