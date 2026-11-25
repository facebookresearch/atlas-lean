# The list-update adversary

Given a deterministic online list-update algorithm $A$, a
default item $d$, a number $n$ and a state $q$ of $A$, the adversary's sequence is the sequence of
$n$ requests that starts in state $q$, always requests the last item of $A$'s current list, and
then moves $A$ to its next state on that request. If the current list is empty, the default item
$d$ is requested instead.
